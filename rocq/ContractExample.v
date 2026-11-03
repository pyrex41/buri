(* E2E-08 worked example, KLambda level. One recursive higher-order function,
   the KLambda translation (KLambdaEvaluatorRefinement.tr) of the klambda.shen
   definition

     map f xs = (if (cons? xs)
                    (let h (hd xs) (let t (tl xs)
                     (let y (f h) (let r ((map f) t) (cons y r)))))
                    ())

   is given one total-correctness contract, derived once in the calculus and
   validated by rec_total with the explicit measure "length of xs". The
   contract is parametric in the closure's effect: f maps each integer z to
   (g z) while performing one Step on the store and preserving an invariant
   Inv. It is then instantiated twice:

   * main_mut: a closure that increments a mutable global counter with
     value/set; the program returns the mapped list paired with the final
     counter, which is proved to equal the list length (this file).
   * the pure doubling closure inside the klambda.shen subset; that instance is
     transported to the captured evaluator in ContractTransport.

   All theorems are universal (every integer list, every profile, every
   resource policy covering the profile's limits, every deterministic
   environment); nothing here is a ground derivation. *)
From Coq Require Import List ZArith NArith String Bool Lia.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory
 KLambdaEvaluatorCapture KLambdaEvaluatorRefinement ContractLogic ContractPrims.
Import ListNotations.
Module ContractExample.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics
 ContractLogic.ContractLogic ContractPrims.ContractPrims.
Module C := KLambdaEvaluatorCapture.KLambdaEvaluatorCapture.
Module R := KLambdaEvaluatorRefinement.KLambdaEvaluatorRefinement.

(* ---------- the program ---------- *)
Definition map_term : C.term :=
 C.TIf (C.TPrim "cons?" [C.TVar "xs"])
  (C.TLet "h" (C.TPrim "hd" [C.TVar "xs"])
   (C.TLet "t" (C.TPrim "tl" [C.TVar "xs"])
    (C.TLet "y" (C.TApply (C.TVar "f") (C.TVar "h"))
     (C.TLet "r" (C.TApply (C.TApply (C.TGlobal "map") (C.TVar "f")) (C.TVar "t"))
      (C.TPrim "cons" [C.TVar "y"; C.TVar "r"])))))
  (C.TLit C.RNil).
Definition map_params : list name := [of_string "f"; of_string "xs"].
Definition map_body : expr := R.tr map_term.
Definition mapn : name := R.fname "map".

Definition consp := of_string "cons?". Definition hdn := of_string "hd". Definition tln := of_string "tl".
Definition consn := of_string "cons". Definition plusn := of_string "+".
Definition valuen := of_string "value". Definition setn := of_string "set".

Fixpoint ilist (l : list Z) : value := match l with
 | [] => VNil | z :: l => VCons (VNum (NInt z)) (ilist l) end.
Fixpoint vlen (v : value) : nat := match v with VCons _ d => S (vlen d) | _ => 0 end.
Lemma vlen_ilist : forall l, vlen (ilist l) = List.length l.
Proof. induction l; cbn; auto. Qed.
Lemma ilist_inj : forall a b, ilist a = ilist b -> a = b.
Proof. induction a as [|x a IH]; destruct b as [|y b]; cbn; intro E; try discriminate; auto.
 injection E as -> E. f_equal; auto. Qed.

(* Store facts the contracts rely on. *)
Definition map_bound (s : store) := lookup mapn (gfuns s) = Some (FUser map_params map_body).
Definition base_prims (s : store) :=
 lookup consp (gfuns s) = Some (FPrim PConsP) /\ lookup hdn (gfuns s) = Some (FPrim PHd) /\
 lookup tln (gfuns s) = Some (FPrim PTl) /\ lookup consn (gfuns s) = Some (FPrim PCons) /\
 lookup plusn (gfuns s) = Some (FPrim PAdd).

Ltac pre_ok := let s := fresh "s" in let H := fresh "H" in intros s H; first [exact H | subst s; reflexivity | auto].
Ltac exn_ok := let x := fresh "x" in let s := fresh "s" in let t := fresh "t" in let H := fresh "H" in
 intros x s t H; first [exact H | destruct H | contradiction | auto].
Section Derived.
Variable P : profile.
Variable RP : resource -> Prop.
Definition exact (v : value) (s1 : store) : post := fun w s t => w = v /\ s = s1 /\ t = [].
Definition nothing : epost := fun _ _ _ => False.
Definition atoms (rho : lenv) := Forall2 (fun a v => atom rho a = Some v).

Lemma d_atom : forall m G rho e v s0 E, atom rho e = Some v ->
 deriv P RP m G (fun s => s = s0) rho e (exact v s0) E.
Proof.
 intros m G rho e v s0 E A. eapply r_conseq; [exact (r_val P RP m G rho e v (exact v s0) E A)| |auto|auto].
 intros s ->; repeat split.
Qed.

Lemma dargs_conseq : forall m G Pre rho es tg Qs E, dargs P RP m G Pre rho es tg Qs E ->
 forall Qs', (forall vs s t, Qs vs s t -> Qs' vs s t) -> dargs P RP m G Pre rho es tg Qs' E.
Proof.
 intros m G Pre rho es tg Qs E D; induction D as [Pre rho a tg Qs E D|Pre rho a a' rest tg Rr Qs E D _ IH]; intros Qs' H.
 - apply da_one. eapply r_conseq; [exact D|auto|cbn; auto|auto].
 - eapply da_cons; [exact D|]. intros v s1 t1 Rv. apply (IH v s1 t1 Rv). intros vs s t Hq; apply H; exact Hq.
Qed.

Lemma d_args : forall m G rho es vs s0 tg E, atoms rho es vs -> es <> [] ->
 dargs P RP m G (fun s => s = s0) rho es tg (fun ws s t => ws = vs /\ s = s0 /\ t = []) E.
Proof.
 intros m G rho es vs s0 tg E F; induction F as [|a v es vs A F IH]; intro N; [contradiction|].
 destruct es as [|a' es].
 - inversion F; subst. apply da_one. eapply r_conseq; [exact (d_atom m G rho a v s0 E A)|auto| |auto].
   intros w s t (-> & -> & ->). repeat split.
 - eapply da_cons; [exact (d_atom m G rho a v s0 E A)|]. intros w s1 t1 (-> & -> & ->).
   eapply dargs_conseq; [apply IH; discriminate|]. intros ws s t (-> & -> & ->). repeat split.
Qed.

Lemma d_prim : forall m G rho f p es vs s0 v s1 E, In (prim_spec P RP f p) G -> atoms rho es vs -> es <> [] ->
 lookup f (gfuns s0) = Some (FPrim p) -> List.length vs = prim_arity p ->
 prim_rule P p vs s0 = PDone (ORet v s1) ->
 deriv P RP m G (fun s => s = s0) rho (ECall f es) (exact v s1) E.
Proof.
 intros m G rho f p es vs s0 v s1 E I A N Lk Ln Rr.
 eapply r_call; [exact (d_args m G rho es vs s0 (TCall f) E A N)|].
 intros ws s t (-> & -> & ->). change (VPartial f []) with (VPartial (c_name (prim_spec P RP f p)) []).
 apply aj_ctx; [exact I|]. intros s ->. cbn [c_pre c_post c_exn prim_spec app]. rewrite Rr. split; [auto|split].
 - intros w s' t' [-> Rw]. injection Rw as <- <-. repeat split.
 - intros x s' t' (_ & _ & Rx). discriminate.
Qed.

Lemma d_let : forall m G rho x a b v s0 s1 Q E,
 deriv P RP m G (fun s => s = s0) rho a (exact v s1) E ->
 deriv P RP m G (fun s => s = s1) ((x, v) :: rho) b Q E ->
 deriv P RP m G (fun s => s = s0) rho (ELet x a b) Q E.
Proof. intros. eapply r_let; [eassumption|]. intros w s t (-> & -> & ->). assumption. Qed.

Lemma d_if : forall m G rho c a b bb s0 s1 Q E,
 deriv P RP m G (fun s => s = s0) rho c (exact (VBool bb) s1) E ->
 deriv P RP m G (fun s => s = s1) rho (if bb then a else b) Q E ->
 deriv P RP m G (fun s => s = s0) rho (EIf c a b) Q E.
Proof.
 intros m G rho c a b bb s0 s1 Q E Dc Db. eapply r_if; [exact Dc| | |].
 - intros s t (Eb & -> & ->). destruct bb; [exact Db|discriminate].
 - intros s t (Eb & -> & ->). destruct bb; [discriminate|exact Db].
 - intros v s t (-> & _ & _) N. exfalso; exact (N bb eq_refl).
Qed.

Lemma d_app1 : forall m G rho hd a fv va s0 s1 s2 Q E,
 deriv P RP m G (fun s => s = s0) rho hd (exact fv s1) E ->
 deriv P RP m G (fun s => s = s1) rho a (exact va s2) E ->
 appj P RP m G fv [va] (fun s => s = s2) Q E ->
 deriv P RP m G (fun s => s = s0) rho (EApp hd [a]) Q E.
Proof.
 intros m G rho hd a fv va s0 s1 s2 Q E Dh Da J.
 eapply r_app with (Qs := fun _ _ ws s t => ws = [va] /\ s = s2 /\ t = []); [exact Dh| |].
 - intros f' s' t' (-> & -> & ->). apply da_one. eapply r_conseq; [exact Da|auto| |auto].
   intros w s t (-> & -> & ->). repeat split.
 - intros f' s' t' vs s3 t3 (-> & -> & ->) (-> & -> & ->). exact J.
Qed.
End Derived.

(* ---------- the map contract ---------- *)
Section MapProof.
Variable P : profile.
Variable RP : resource -> Prop.
Variable g : Z -> Z.
Variable Step : store -> store -> Prop.
Variable Inv : store -> Prop.
Hypothesis StepOk : forall s0 s1, Inv s0 -> Step s0 s1 -> Inv s1 /\ gfuns s1 = gfuns s0.
Hypothesis InvBound : forall s, Inv s -> map_bound s /\ base_prims s.

Fixpoint iter (n : nat) (s0 s : store) : Prop := match n with
 | O => s = s0 | S n => exists s1, Step s0 s1 /\ iter n s1 s end.
Lemma iter_inv : forall n s0 s, Inv s0 -> iter n s0 s -> Inv s /\ gfuns s = gfuns s0.
Proof.
 induction n as [|n IH]; cbn; intros s0 s I0 It; [subst; auto|].
 destruct It as (s1 & St & It). destruct (StepOk _ _ I0 St) as [I1 E1].
 destruct (IH _ _ I1 It) as [I2 E2]. split; [exact I2|congruence].
Qed.

(* f computes g on integers, performing exactly one Step and raising nothing. *)
Definition fspec (fv : value) := forall z s0, Inv s0 ->
 app_sem P RP Total fv [VNum (NInt z)] (fun s => s = s0)
   (fun v s1 t => v = VNum (NInt (g z)) /\ Step s0 s1 /\ t = []) nothing.

Definition map_spec : cspec := CSpec mapn
 (fun vs s => exists fv l, vs = [fv; ilist l] /\ Inv s /\ fspec fv)
 (fun vs s0 v s t => exists fv l, vs = [fv; ilist l] /\ v = ilist (map g l) /\ iter (List.length l) s0 s /\ t = [])
 (fun _ _ _ _ _ => False).
Definition map_meas (vs : list value) (_ : store) : nat := match vs with [_; xs] => vlen xs | _ => 0 end.
Definition Tmap := TDef (FDef map_spec map_params map_body) map_meas.

Definition Gx : list cspec :=
 [prim_spec P RP consp PConsP; prim_spec P RP hdn PHd; prim_spec P RP tln PTl; prim_spec P RP consn PCons;
  prim_spec P RP plusn PAdd; prim_spec P RP valuen PValue; prim_spec P RP setn PSet].
Lemma Gx_valid : forall n, ctx_at P RP Total n Gx.
Proof. intros n c I. repeat (destruct I as [<-|I]; [apply prim_spec_valid|]). contradiction. Qed.

Lemma in_below : forall b c, In c Gx -> In c (ctx_below [Tmap] Gx b).
Proof. intros b c I; apply in_or_app; right; exact I. Qed.
Ltac gx := apply in_below; cbn [Gx In]; tauto.

Lemma map_binds : binds (td_def Tmap).
Proof. intros vs s (fv & l & -> & Iv & _). split; [exact (proj1 (InvBound s Iv))|reflexivity]. Qed.

Lemma map_body_ok : body_ok_total P RP [Tmap] Gx Tmap.
Proof.
 intros vs s0 (fv & l & -> & I0 & Fs). destruct (InvBound s0 I0) as [Mb (Pc & Ph & Pt & Pk & _)].
 cbn [td_def fd_params fd_body fd_spec Tmap combine map_params c_post c_exn map_spec td_meas map_meas].
 rewrite vlen_ilist. unfold map_body, map_term. cbn [R.tr map R.lit].
 destruct l as [|z l].
 - (* empty list *)
   eapply d_if with (bb := false) (s1 := s0).
   + eapply d_prim with (p := PConsP) (vs := [VNil]); [gx|repeat constructor|discriminate|exact Pc|reflexivity|reflexivity].
   + eapply r_conseq; [apply d_atom; reflexivity|pre_ok| |exn_ok].
     intros v s t (-> & -> & ->). exists fv, []; cbn; auto.
 - (* z :: l *)
   eapply d_if with (bb := true) (s1 := s0).
   + eapply d_prim with (p := PConsP) (vs := [ilist (z :: l)]); [gx|repeat constructor|discriminate|exact Pc|reflexivity|reflexivity].
   + eapply d_let.
     { eapply d_prim with (p := PHd) (vs := [ilist (z :: l)]); [gx|repeat constructor|discriminate|exact Ph|reflexivity|reflexivity]. }
     eapply d_let.
     { eapply d_prim with (p := PTl) (vs := [ilist (z :: l)]); [gx|repeat constructor|discriminate|exact Pt|reflexivity|reflexivity]. }
     eapply r_let with (R := fun v s1 t => v = VNum (NInt (g z)) /\ Step s0 s1 /\ t = []).
     { eapply d_app1; [apply d_atom; reflexivity|apply d_atom; reflexivity|]. apply aj_sem. exact (Fs z s0 I0). }
     intros y s1 t1 (-> & St & ->). destruct (StepOk _ _ I0 St) as [I1 G1].
     eapply r_let with (R := c_post map_spec [fv; ilist l] s1).
     { eapply d_app1 with (fv := VPartial mapn [fv]) (s1 := s1); [| apply d_atom; reflexivity |].
       - eapply d_app1 with (fv := VPartial mapn []) (s1 := s1); [|apply d_atom; reflexivity|].
         + apply r_call0. apply aj_partial. intros s ->. exists (FUser map_params map_body).
           split; [unfold map_bound in Mb; rewrite G1; exact Mb|]. split; [cbn; lia|repeat split].
         + apply aj_partial. intros s ->. exists (FUser map_params map_body).
           split; [unfold map_bound in Mb; rewrite G1; exact Mb|]. split; [cbn; lia|repeat split].
       - change (VPartial mapn [fv]) with (VPartial (c_name (restrict Tmap (S (List.length l)))) [fv]).
         apply aj_ctx; [apply in_or_app; left; left; reflexivity|].
         intros s ->. split; [|split; [intros v s' t' H; exact H|intros x s' t' []]].
         cbn [restrict c_pre c_name Tmap td_def fd_spec map_spec app td_meas map_meas].
         split; [exists fv, l; auto|rewrite vlen_ilist; lia]. }
     intros rv s2 t2 (fv' & l' & Ev & -> & It & ->). injection Ev as <- El. apply ilist_inj in El. subst l'.
     destruct (iter_inv _ _ _ I1 It) as [I2 G2].
     eapply r_conseq.
     { eapply d_prim with (s0 := s2) (p := PCons) (vs := [VNum (NInt (g z)); ilist (map g l)]);
         [gx|repeat constructor|discriminate| |reflexivity|reflexivity].
       rewrite G2, G1; exact Pk. }
     { pre_ok. }
     { intros v s t (-> & -> & ->). exists fv, (z :: l). cbn. repeat split. exists s1; auto. }
     { exn_ok. }
Qed.

Theorem map_ctx_valid : policy_ok P RP -> forall n, ctx_at P RP Total n (map_spec :: Gx).
Proof.
 intros PO n. apply (rec_total P RP PO [Tmap] Gx Gx_valid).
 - constructor; [exact map_binds|constructor].
 - constructor; [exact map_body_ok|constructor].
Qed.
End MapProof.

(* ---------- instance 1: a closure with a mutable global counter ---------- *)
Definition countn := of_string "count".
Definition xn := of_string "x". Definition cn := of_string "c". Definition c1n := of_string "c1".
Definition un := of_string "u". Definition rn := of_string "r".
(* (lambda x (let c (value count) (let c1 (+ c 1) (let u (set count c1) (+ x x))))) *)
Definition tick : expr :=
 ELet cn (ECall valuen [ESym countn])
  (ELet c1n (ECall plusn [EVar cn; ENum (NInt 1)])
   (ELet un (ECall setn [ESym countn; EVar c1n])
    (ECall plusn [EVar xn; EVar xn]))).
Fixpoint rlist (l : list Z) : C.rv := match l with [] => C.RNil | z :: l => C.RPair (C.RInt z) (rlist l) end.
(* (let u (set count 0) (let r ((map (lambda x tick)) L) (let c (value count) (cons r c)))) *)
Definition main_mut (l : list Z) : expr :=
 ELet un (ECall setn [ESym countn; ENum (NInt 0)])
  (ELet rn (EApp (EApp (ECall mapn []) [ELam xn tick]) [R.lit (rlist l)])
   (ELet cn (ECall valuen [ESym countn])
    (ECall consn [EVar rn; EVar cn]))).

Definition mut_prims (s : store) := base_prims s /\
 lookup valuen (gfuns s) = Some (FPrim PValue) /\ lookup setn (gfuns s) = Some (FPrim PSet).
Definition counter (k : Z) (s : store) := lookup countn (gvals s) = Some (VNum (NInt k)).
Definition mut_inv (s : store) := map_bound s /\ mut_prims s /\ exists k, counter k s.
Definition mut_step (s0 s1 : store) := exists k, counter k s0 /\ counter (k + 1) s1 /\ gfuns s1 = gfuns s0.

Lemma mut_step_ok : forall s0 s1, mut_inv s0 -> mut_step s0 s1 -> mut_inv s1 /\ gfuns s1 = gfuns s0.
Proof.
 intros s0 s1 (Mb & Mp & _) (k & _ & K1 & E). unfold mut_inv, map_bound, mut_prims, base_prims in *.
 split; [rewrite E; split; [exact Mb|split; [exact Mp|eauto]]|exact E].
Qed.
Lemma mut_inv_bound : forall s, mut_inv s -> map_bound s /\ base_prims s.
Proof. intros s (Mb & Mp & _); split; [exact Mb|exact (proj1 Mp)]. Qed.

Lemma iter_counter : forall n s0 s k, counter k s0 -> iter mut_step n s0 s -> counter (k + Z.of_nat n) s.
Proof.
 induction n as [|n IH]; intros s0 s k K It.
 - cbn [iter] in It; subst. rewrite Z.add_0_r; exact K.
 - cbn [iter] in It. destruct It as (s1 & (k' & K0 & K1 & _) & It). unfold counter in K, K0. rewrite K in K0.
   injection K0 as <-. rewrite Nat2Z.inj_succ.
   replace (k + Z.succ (Z.of_nat n))%Z with ((k + 1) + Z.of_nat n)%Z by lia. eapply IH; eauto.
Qed.

Section Mutable.
Variable P : profile.
Variable RP : resource -> Prop.
Hypothesis PO : policy_ok P RP.
Definition dbl (z : Z) := (z + z)%Z.
Definition GM := map_spec P RP dbl mut_step mut_inv :: Gx P RP.
Lemma GM_valid : forall n, ctx_at P RP Total n GM.
Proof. exact (map_ctx_valid P RP dbl mut_step mut_inv mut_step_ok mut_inv_bound PO). Qed.
Ltac gm := cbn [GM Gx In]; tauto.

Lemma lit_ok : forall G rho l s0, In (prim_spec P RP consn PCons) G -> lookup consn (gfuns s0) = Some (FPrim PCons) ->
 deriv P RP Total G (fun s => s = s0) rho (R.lit (rlist l)) (exact (ilist l) s0) nothing.
Proof.
 intros G rho l s0 I Lk; induction l as [|z l IH]; cbn [rlist R.lit].
 - apply d_atom; reflexivity.
 - eapply r_call with (Qs := fun ws s t => ws = [VNum (NInt z); ilist l] /\ s = s0 /\ t = []).
   + eapply da_cons; [apply d_atom; reflexivity|]. intros v s1 t1 (-> & -> & ->).
     apply da_one. eapply r_conseq; [exact IH|pre_ok| |exn_ok]. intros w s t (-> & -> & ->). repeat split.
   + intros ws s t (-> & -> & ->).
     apply (aj_ctx P RP Total G (prim_spec P RP consn PCons) []); [exact I|]. intros s ->. split; [split; [exact Lk|split; [reflexivity|exact Logic.I]]|split].
     * intros w s' t' [-> Rw]. cbn in Rw. injection Rw as <- <-. repeat split.
     * intros x s' t' (_ & _ & Rx). discriminate.
Qed.

(* The counter closure meets the map contract's function premise. *)
Lemma tick_spec : forall rho, fspec P RP dbl mut_step mut_inv (VLam xn tick rho).
Proof.
 intros rho z s0 I0. destruct I0 as (Mb & (Bp & Pv & Ps) & k & K).
 destruct Bp as (_ & _ & _ & _ & Pp).
 eapply (appj_sound P RP PO Total (Gx P RP)); [apply Gx_valid|]. apply aj_lam. unfold tick.
 eapply d_let.
 { eapply d_prim with (p := PValue) (vs := [VSym countn]); [cbn; tauto|repeat constructor|discriminate|exact Pv|reflexivity|].
   unfold counter in K. cbn [prim_rule rule_value]. rewrite K. reflexivity. }
 eapply d_let.
 { eapply d_prim with (p := PAdd) (vs := [VNum (NInt k); VNum (NInt 1)]); [cbn; tauto|repeat constructor|discriminate|exact Pp|reflexivity|reflexivity]. }
 eapply d_let.
 { eapply d_prim with (p := PSet) (vs := [VSym countn; VNum (NInt (k + 1))]); [cbn; tauto|repeat constructor|discriminate|exact Ps|reflexivity|reflexivity]. }
 eapply r_conseq.
 { eapply d_prim with (s0 := Store (heap s0) ((countn, VNum (NInt (k + 1))) :: gvals s0) (gfuns s0))
     (p := PAdd) (vs := [VNum (NInt z); VNum (NInt z)]); [cbn; tauto|repeat constructor|discriminate|exact Pp|reflexivity|reflexivity]. }
 { pre_ok. }
 { intros v s t (-> & -> & ->). split; [reflexivity|split; [|reflexivity]].
   exists k; split; [exact K|split; reflexivity]. }
 { exn_ok. }
Qed.

Definition mut_post (l : list Z) : post := fun v s t =>
 v = VCons (ilist (map dbl l)) (VNum (NInt (Z.of_nat (List.length l)))) /\ t = [].

Lemma main_mut_deriv : forall l s0, map_bound s0 -> mut_prims s0 ->
 deriv P RP Total GM (fun s => s = s0) [] (main_mut l) (mut_post l) nothing.
Proof.
 intros l s0 Mb Mp. pose proof Mp as (Bp & Pv & Ps). pose proof Bp as (_ & _ & _ & Pk & _).
 unfold main_mut. set (s1 := Store (heap s0) ((countn, VNum (NInt 0)) :: gvals s0) (gfuns s0)).
 assert (I1 : mut_inv s1) by (split; [exact Mb|split; [exact Mp|exists 0%Z; reflexivity]]).
 eapply d_let.
 { eapply d_prim with (p := PSet) (vs := [VSym countn; VNum (NInt 0)]); [gm|repeat constructor|discriminate|exact Ps|reflexivity|reflexivity]. }
 eapply r_let with (R := c_post (map_spec P RP dbl mut_step mut_inv) [VLam xn tick [(un, VNum (NInt 0))]; ilist l] s1).
 { eapply d_app1 with (fv := VPartial mapn [VLam xn tick [(un, VNum (NInt 0))]]) (s1 := s1).
   - eapply d_app1 with (fv := VPartial mapn []) (s1 := s1); [|apply d_atom; reflexivity|].
     + apply r_call0. apply aj_partial. intros s ->. exists (FUser map_params map_body). split; [exact Mb|split; [cbn; lia|repeat split]].
     + apply aj_partial. intros s ->. exists (FUser map_params map_body). split; [exact Mb|split; [cbn; lia|repeat split]].
   - apply (lit_ok GM); [cbn [GM Gx In]; tauto|exact Pk].
   - apply (aj_ctx P RP Total GM (map_spec P RP dbl mut_step mut_inv) [VLam xn tick [(un, VNum (NInt 0))]]);
       [left; reflexivity|].
     intros s ->. split; [|split; [intros v s' t' H; exact H|intros x s' t' []]].
     exists (VLam xn tick [(un, VNum (NInt 0))]), l. split; [reflexivity|split; [exact I1|apply tick_spec]]. }
 intros rv s2 t2 (fv' & l' & Ev & -> & It & ->). injection Ev as <- El. apply ilist_inj in El. subst l'.
 destruct (iter_inv mut_step mut_inv mut_step_ok _ _ _ I1 It) as [_ G2].
 assert (K2 : counter (Z.of_nat (List.length l)) s2)
   by (rewrite <- (Z.add_0_l (Z.of_nat _)); apply (iter_counter (List.length l) s1 s2 0%Z); [reflexivity|exact It]).
 eapply d_let.
 { eapply d_prim with (p := PValue) (vs := [VSym countn]); [gm|repeat constructor|discriminate| |reflexivity|].
   - rewrite G2; exact Pv.
   - unfold counter in K2. cbn [prim_rule rule_value]. rewrite K2. reflexivity. }
 eapply r_conseq.
 { eapply d_prim with (s0 := s2) (p := PCons) (vs := [ilist (map dbl l); VNum (NInt (Z.of_nat (List.length l)))]);
     [gm|repeat constructor|discriminate| |reflexivity|reflexivity].
   rewrite G2; exact Pk. }
 { pre_ok. }
 { intros v s t (-> & -> & ->). split; reflexivity. }
 { exn_ok. }
Qed.

(* Total correctness of main_mut in the calculus semantics. *)
Theorem main_mut_total : forall l s0, map_bound s0 -> mut_prims s0 ->
 triple P RP Total (fun s => s = s0) [] (main_mut l) (mut_post l) nothing.
Proof. intros l s0 Mb Mp. exact (deriv_sound P RP PO Total GM _ _ _ _ _ GM_valid (main_mut_deriv l s0 Mb Mp)). Qed.

(* The same, as maximal behaviors of the closed KLambda system: against any
   environment that answers every request, every behavior terminates, and its
   outcome is the mapped list paired with the counter value (length l), or a
   resource failure admitted by the policy; no exception, divergence,
   reaction or wrong state. *)
Theorem main_mut_behaviors : forall (W : Type) (O : W -> request -> response -> W -> Prop) (tk : W -> W) (l : list Z) (s0 : store) (w : W),
 map_bound s0 -> mut_prims s0 -> (forall w q, exists r w', O w q r w') ->
 (forall b, KLMetatheory.behaviors W O (none W) tk P (Cfg (Eval [] (main_mut l)) [] s0) w b ->
   exists t o, b = Terminates t o /\ match o with
   | Normal v => v = VCons (ilist (map dbl l)) (VNum (NInt (Z.of_nat (List.length l)))) /\ t = []
   | ResourceOut r => RP r
   | _ => False end) /\ exists t o, KLMetatheory.behaviors W O (none W) tk P (Cfg (Eval [] (main_mut l)) [] s0) w (Terminates t o).
Proof.
 intros W O tk l s0 w Mb Mp OT.
 destruct (total_meaning P RP W O tk _ [] (main_mut l) (mut_post l) nothing s0 w PO OT (main_mut_total l s0 Mb Mp) eq_refl)
   as [A B]. split; [|exact B].
 intros b Bb. destruct (A b Bb) as (t & o & -> & Ho). exists t, o; split; [reflexivity|].
 destruct o; cbn in Ho; try contradiction; [destruct Ho as (s & Hq); exact Hq|destruct Ho as (s & [])|exact Ho].
Qed.

(* Evaluator form: KLMetatheory.run with any deterministic environment
   returns this decided verdict for some fuel. *)
Theorem main_mut_run : forall W respond tick l s0 w, map_bound s0 -> mut_prims s0 ->
 exists n t o, krun P W respond tick n (Cfg (Eval [] (main_mut l)) [] s0) w = VDone t o /\ match o with
   | Normal v => v = VCons (ilist (map dbl l)) (VNum (NInt (Z.of_nat (List.length l)))) /\ t = []
   | ResourceOut r => RP r
   | _ => False end.
Proof.
 intros W respond tick l s0 w Mb Mp.
 destruct (total_run P RP W respond tick _ [] (main_mut l) (mut_post l) nothing s0 w (main_mut_total l s0 Mb Mp) eq_refl)
   as (n & t & o & Rn & Ho). exists n, t, o; split; [exact Rn|].
 destruct o; cbn in Ho; try contradiction; [destruct Ho as (s & Hq); exact Hq|destruct Ho as (s & [])|exact Ho].
Qed.
End Mutable.
End ContractExample.
