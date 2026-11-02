(* Port-fix lane: the PATCHED |shen-cl.multiply| (Shen-CL 4844072d
   src/primitives.lsp blob f9b11c8a with ports/patches/shen-cl-primitives.diff
   applied; bytes packaged by scripts/package-patched.py into
   PatchedPrimitiveSources.v, read here by PortReader in CL mode and
   admitted by computed equality with the reviewed expected AST).

   PROFILE CHOICE, not a stock-port bug fix: upstream deliberately keeps
   [* 0 <non-number>] = 0 (shen-cl tests/primitives-tests.shen asserts it),
   so the stock behaviour is refuted only against Búri's stricter arithmetic
   profile (KLSemantics.rule_arith: * on a non-number is a domain error).
   The patch makes the zero shortcut require two numbers; upstream would
   also have to change that test (ports/patches/shen-cl-primitives-tests.diff).

   Theorems quantify over every host table satisfying the named SBCL
   contracts: CLWrappers.sbcl_arith_ops (unchanged) and the non-number
   classification contracts [sbcl_nonnumber_ops] below. *)
From Coq Require Import String List ZArith Bool Lia.
From Buri Require Import PortReader PatchedPrimitiveSources KLSyntax KLValue KLSemantics.
From Buri Require CLLowering CLWrappers.
Import ListNotations.
Module CLMultiplyPatched.
Module R := PortReader.PortReader.
Module W := CLWrappers.CLWrappers.
Open Scope string_scope.
Notation sv := CLLowering.sv.
Notation VSym := CLLowering.VSym.
Notation VNum := CLLowering.VNum.
Notation VNil := CLLowering.VNil.
Notation SL := W.SL.
Notation Sy := W.Sy.

Definition patched_multiply_body := SL [Sy "COND";
 SL [SL [Sy "AND"; W.fx "X"; W.fx "Y"]; W.xy "*"];
 SL [SL [Sy "AND"; W.df "X"; W.df "Y"]; SL [Sy "IF"; SL [Sy "OR"; SL [Sy "ZEROP"; Sy "X"]; SL [Sy "ZEROP"; Sy "Y"]]; VNum "0"; W.xy "*"]];
 SL [SL [Sy "AND"; SL [Sy "NUMBERP"; Sy "X"]; SL [Sy "NUMBERP"; Sy "Y"];
         SL [Sy "OR"; SL [Sy "ZEROP"; Sy "X"]; SL [Sy "ZEROP"; Sy "Y"]]]; VNum "0"];
 SL [Sy "T"; SL [Sy "*"; W.dp "X"; W.dp "Y"]]].
Definition admission_of (src : string) : option sv :=
 match R.read true src with
 | Some [d] => match W.defun_of d with
   | Some ("shen-cl.multiply", (["X"; "Y"], [b])) =>
     if CLLowering.sv_eqb b patched_multiply_body then Some b else None
   | _ => None end
 | _ => None end.
Theorem patched_multiply_admitted : admission_of patched_multiply_source = Some patched_multiply_body.
Proof. vm_compute. reflexivity. Qed.
(* The patched body differs from the admitted stock body. *)
Theorem patched_differs_from_stock : CLLowering.sv_eqb patched_multiply_body W.multiply_body = false.
Proof. vm_compute. reflexivity. Qed.

(* Named SBCL classification contracts for non-number first-order data
   (symbols, strings, NIL, conses). COERCE of such a datum to DOUBLE-FLOAT
   signals a condition (the payload is not modelled). *)
Record sbcl_nonnumber_ops (h : string -> list sv -> W.cres) : Prop := {
 nn_numberp : forall v, W.cdata v -> h "NUMBERP" [v] = W.CRet (W.hb (W.is_num v));
 nn_fixnum : forall v, W.cdata v -> W.is_num v = false -> h "TYPEP" [v; VSym "FIXNUM"] = W.CRet VNil;
 nn_double : forall v, W.cdata v -> W.is_num v = false -> h "TYPEP" [v; VSym "DOUBLE-FLOAT"] = W.CRet VNil;
 nn_int_or_double : forall v, W.cdata v -> W.is_num v = false ->
   h "TYPEP" [v; SL [Sy "OR"; Sy "INTEGER"; Sy "DOUBLE-FLOAT"]] = W.CRet VNil;
 nn_coerce : forall v, W.cdata v -> W.is_num v = false -> exists e, h "COERCE" [v; VSym "DOUBLE-FLOAT"] = W.CRaise e }.

Ltac plain_rw P := let Q := fresh in pose proof (W.plain_split _ P) as Q;
 destruct Q as [Q1 [Q2 [Q3 [Q4 [Q5 [Q6 [Q8 Q7]]]]]]];
 cbn [W.ceval R.to_list W.SL fold_right option_map W.Sy]; rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q8, Q7.
Ltac host := first [eapply W.ce_host2; [reflexivity|reflexivity| | | ] | eapply W.ce_host1; [reflexivity|reflexivity| | ]].
Ltac cvar := apply W.ce_var; reflexivity.

Section Patched.
Variables (h : string -> list sv -> W.cres) (ratio to_double : Z -> Z -> sv) (one_d div0 : sv).
Hypothesis A : W.sbcl_arith_ops h ratio to_double one_d div0.
Hypothesis NN : sbcl_nonnumber_ops h.

Lemma raise_first : forall m env g x y e, W.plain g = true ->
 W.ceval m h env x = W.CRaise e -> W.ceval (S m) h env (SL [Sy g; x; y]) = W.CRaise e.
Proof. intros m env g x y e P Hx. plain_rw P. rewrite Hx. reflexivity. Qed.
Lemma raise_second : forall m env g x y v e, W.plain g = true ->
 W.ceval m h env x = W.CRet v -> W.ceval m h env y = W.CRaise e -> W.ceval (S m) h env (SL [Sy g; x; y]) = W.CRaise e.
Proof. intros m env g x y v e P Hx Hy. plain_rw P. rewrite Hx, Hy. reflexivity. Qed.
Lemma dp_raise : forall m env x v, W.cdata v -> W.is_num v = false -> W.ceval (S (S (S m))) h env x = W.CRet v ->
 exists e, W.ceval (S (S (S (S m)))) h env (SL [Sy "shen-cl.double-precision"; x]) = W.CRaise e.
Proof.
 intros m env x v Dv Nv Hx. destruct (nn_coerce h NN v Dv Nv) as [e E]. exists e.
 rewrite (W.ce_def1 _ _ _ _ _ v ["X"] W.double_precision_body) by (reflexivity || exact Hx).
 unfold W.double_precision_body.
 rewrite (W.ce_if _ _ _ _ _ _ VNil) by (host; [cvar|reflexivity|apply (nn_int_or_double h NN); assumption]).
 cbn [W.truthy]. host; [cvar|reflexivity|exact E].
Qed.
Lemma and3_nil : forall m env x y z, W.ceval m h env x = W.CRet VNil ->
 W.ceval (S m) h env (SL [Sy "AND"; x; y; z]) = W.CRet VNil.
Proof. intros. rewrite (W.ce_and3 h m env x y z VNil H). reflexivity. Qed.
Lemma and3_t : forall m env x y z v, W.ceval m h env x = W.CRet v -> W.truthy v = true ->
 W.ceval (S m) h env (SL [Sy "AND"; x; y; z]) = W.ceval (S m) h env (SL [Sy "AND"; y; z]).
Proof. intros. rewrite (W.ce_and3 h m env x y z v H), H0. reflexivity. Qed.

(* On every pair of exact integers the patched wrapper is the exact product
   (the patch changes nothing on numbers). *)
Theorem patched_multiply_int : forall x y n, n >= 10 ->
 W.ceval n h (W.env2 (W.zs x) (W.zs y)) patched_multiply_body = W.CRet (W.zs (x * y)).
Proof.
 intros x y n Hn.
 assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); lia).
 unfold patched_multiply_body. destruct (W.and_fx h ratio to_double one_d div0 A (S (S (S (S (S m))))) x y) as [r [Er _]].
 destruct r.
 - rewrite (W.ce_cond_hit _ _ _ _ _ _ W.T) by (exact Er || reflexivity). host; [cvar|cvar|apply (W.sbcl_mul _ _ _ _ _ A)].
 - rewrite W.ce_cond_miss by exact Er. rewrite W.ce_cond_miss by apply (W.and_df h ratio to_double one_d div0 A).
   assert (NX : W.ceval (S (S (S (S (S (S (S (S m)))))))) h (W.env2 (W.zs x) (W.zs y)) (SL [Sy "NUMBERP"; Sy "X"]) = W.CRet W.T)
     by (host; [cvar|apply (nn_numberp h NN); constructor]).
   assert (NY : W.ceval (S (S (S (S (S (S (S (S m)))))))) h (W.env2 (W.zs x) (W.zs y)) (SL [Sy "NUMBERP"; Sy "Y"]) = W.CRet W.T)
     by (host; [cvar|apply (nn_numberp h NN); constructor]).
   destruct (Z.eqb x 0) eqn:X0.
   + apply Z.eqb_eq in X0; subst.
     rewrite (W.ce_cond_hit _ _ _ _ _ _ W.T); [reflexivity| |reflexivity].
     rewrite (and3_t _ _ _ _ _ W.T NX) by reflexivity.
     rewrite (W.ce_and2 _ _ _ _ _ W.T NY). cbn [W.truthy].
     apply W.ce_or_left with (v := W.T); [|reflexivity]. host; [cvar|apply (W.sbcl_zerop _ _ _ _ _ A)].
   + destruct (Z.eqb y 0) eqn:Y0.
     * apply Z.eqb_eq in Y0; subst. rewrite Z.mul_0_r.
       rewrite (W.ce_cond_hit _ _ _ _ _ _ W.T); [reflexivity| |reflexivity].
       rewrite (and3_t _ _ _ _ _ W.T NX) by reflexivity.
       rewrite (W.ce_and2 _ _ _ _ _ W.T NY). cbn [W.truthy].
       rewrite (W.ce_or2 _ _ _ _ _ VNil) by (host; [cvar|rewrite (W.sbcl_zerop _ _ _ _ _ A), X0; reflexivity]).
       host; [cvar|apply (W.sbcl_zerop _ _ _ _ _ A)].
     * rewrite W.ce_cond_miss.
       2: { rewrite (and3_t _ _ _ _ _ W.T NX) by reflexivity.
            rewrite (W.ce_and2 _ _ _ _ _ W.T NY). cbn [W.truthy].
            rewrite (W.ce_or2 _ _ _ _ _ VNil) by (host; [cvar|rewrite (W.sbcl_zerop _ _ _ _ _ A), X0; reflexivity]).
            host; [cvar|rewrite (W.sbcl_zerop _ _ _ _ _ A), Y0; reflexivity]. }
       rewrite (W.ce_cond_hit _ _ _ _ _ _ W.T) by reflexivity.
       rewrite (W.dp_args h ratio to_double one_d div0 A) by reflexivity. apply (W.sbcl_mul _ _ _ _ _ A).
Qed.

(* A non-number in EITHER position raises (whatever the other argument is),
   exactly where Búri's profile rule for * is a domain error. Contrast:
   CLWrappers.multiply_zero_absorbs_symbol for the stock wrapper. *)
Theorem patched_multiply_rejects_nonnumber : forall a b n, W.cdata a -> W.cdata b ->
 (W.is_num a = false \/ W.is_num b = false) -> n >= 10 ->
 exists e, W.ceval n h (W.env2 a b) patched_multiply_body = W.CRaise e.
Proof.
 intros a b n Da Db Hab Hn.
 assert (exists m, n = S (S (S (S (S (S (S (S (S (S m)))))))))) as [m ->] by (exists (n - 10); lia).
 unfold patched_multiply_body.
 assert (CA : forall v, W.cdata v -> W.is_num v = true -> exists z, v = W.zs z) by (intros; apply W.cdata_num; assumption).
 destruct (W.is_num a) eqn:Na.
 - (* a is an integer, so b is not a number *)
   destruct Hab as [Hab|Nb]; [discriminate|]. destruct (CA a Da Na) as [z ->].
   destruct (W.sbcl_fixnum_int _ _ _ _ _ A z) as [r Er].
   rewrite W.ce_cond_miss.
   2: { rewrite (W.ce_and2 _ _ _ _ _ (W.hb r)) by (host; [cvar|reflexivity|exact Er]).
        destruct r; cbn [W.truthy W.hb]; [|reflexivity]. host; [cvar|reflexivity|apply (nn_fixnum h NN); assumption]. }
   rewrite W.ce_cond_miss.
   2: { rewrite (W.ce_and2 _ _ _ _ _ VNil) by (host; [cvar|reflexivity|apply (W.sbcl_double_int _ _ _ _ _ A)]). reflexivity. }
   rewrite W.ce_cond_miss.
   2: { rewrite (and3_t _ _ _ _ _ W.T) by (reflexivity || (host; [cvar|apply (nn_numberp h NN); constructor])).
        rewrite (W.ce_and2 _ _ _ _ _ VNil) by (host; [cvar|rewrite (nn_numberp h NN), Nb by exact Db; reflexivity]).
        reflexivity. }
   rewrite (W.ce_cond_hit _ _ _ _ _ _ W.T) by reflexivity.
   destruct (dp_raise (S (S (S (S m)))) (W.env2 (W.zs z) b) (Sy "Y") b Db Nb) as [e E]; [cvar|].
   exists e. eapply raise_second; [reflexivity| |exact E].
   apply (W.dp_int h ratio to_double one_d div0 A). cvar.
 - (* a is not a number *)
   rewrite W.ce_cond_miss.
   2: { rewrite (W.ce_and2 _ _ _ _ _ VNil) by (host; [cvar|reflexivity|apply (nn_fixnum h NN); assumption]). reflexivity. }
   rewrite W.ce_cond_miss.
   2: { rewrite (W.ce_and2 _ _ _ _ _ VNil) by (host; [cvar|reflexivity|apply (nn_double h NN); assumption]). reflexivity. }
   rewrite W.ce_cond_miss.
   2: { apply and3_nil. host; [cvar|rewrite (nn_numberp h NN), Na by exact Da; reflexivity]. }
   rewrite (W.ce_cond_hit _ _ _ _ _ _ W.T) by reflexivity.
   destruct (dp_raise (S (S (S (S m)))) (W.env2 a b) (Sy "X") a Da Na) as [e E]; [cvar|].
   exists e. apply raise_first; [reflexivity|exact E].
Qed.
End Patched.

(* The KLambda profile rule for the same inputs: * on a non-number is the
   domain error dom PMul, in either position (here for a symbol). *)
Theorem profile_multiply_nonnumber : forall Pr st t z,
 KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PMul Z.mul
   [KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt z); KLValue.KLValue.VSym t] st = KLSemantics.KLSemantics.dom KLSyntax.KLSyntax.PMul /\
 KLSemantics.KLSemantics.rule_arith Pr KLSyntax.KLSyntax.PMul Z.mul
   [KLValue.KLValue.VSym t; KLValue.KLValue.VNum (KLSyntax.KLSyntax.NInt z)] st = KLSemantics.KLSemantics.dom KLSyntax.KLSyntax.PMul.
Proof. split; reflexivity. Qed.

(* Anti-vacuity: a concrete host table satisfying both contract records. *)
Definition model_h (f : string) (vs : list sv) : W.cres :=
 if String.eqb f "NUMBERP" then match vs with [v] => W.CRet (W.hb (W.is_num v)) | _ => W.CUnsup end
 else if String.eqb f "COERCE" then match vs with
   | [VNum "1.0"; VSym "DOUBLE-FLOAT"] => W.CRet (CLLowering.VObj 1)
   | [v; VSym "DOUBLE-FLOAT"] => if W.is_num v then W.CUnsup else W.CRaise (CLLowering.VObj 4)
   | _ => W.CUnsup end
 else if String.eqb f "TYPEP" then match vs with
   | [v; t] => if W.is_num v then W.model_arith f vs else match t with
     | VSym "FIXNUM" | VSym "DOUBLE-FLOAT" => W.CRet VNil
     | _ => if CLLowering.sv_eqb t (SL [Sy "OR"; Sy "INTEGER"; Sy "DOUBLE-FLOAT"]) then W.CRet VNil else W.CUnsup end
   | _ => W.CUnsup end
 else W.model_arith f vs.
Theorem model_satisfiable : W.sbcl_arith_ops model_h W.mratio W.mdouble (CLLowering.VObj 1) (CLLowering.VObj 3) /\
 sbcl_nonnumber_ops model_h.
Proof.
 split.
 - destruct W.model_arith_ops as [F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13].
   constructor; intros; unfold model_h; cbn [String.eqb Ascii.eqb Bool.eqb W.is_num W.zs]; try solve [eauto].

 - constructor; intros v Dv; [reflexivity| | | |];
   intro Nv; unfold model_h; cbn [String.eqb Ascii.eqb Bool.eqb]; rewrite Nv;
   try reflexivity.
   destruct v; try reflexivity; try (exists (CLLowering.VObj 4); reflexivity); discriminate Nv.
Qed.
End CLMultiplyPatched.
