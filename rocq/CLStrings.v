(* E2E-17, Wave-D primitives lane: body proofs of the captured Shen-CL string,
   vector-read and intern primitives (Shen-Language/shen-cl 4844072d
   src/primitives.lsp blob f9b11c8a): |pos|, |tlstr|, |n->string|,
   |string->n|, |<-address| and |intern|.

   The exact bytes are packaged by scripts/package-prims2.py into
   Prims2Sources.v, read by the independent PortReader in CL mode, and
   admitted by computed equality with the reviewed ASTs below. The bodies are
   run in CLWrappers' functional evaluator [ceval].

   Every theorem quantifies over EVERY host table [h] satisfying
   CLContracts.cl_host_ops (STRINGP, NOT, INTEGERP) and the individually
   named records [cl_string_ops], [cl_vector_ops] and [cl_intern_ops] below,
   and over every host character encoding [chr]/[cchar] and simple-vector
   encoding [vec]. Nothing here is a theorem about SBCL.

   Modeling boundary (stated, not hidden): the environment binds the CL
   constants the bodies read, the keyword :INITIAL-ELEMENT to itself and
   CHAR-CODE-LIMIT to 1114112 (the pinned SBCL 2.6.8 image value,
   docs/REPRESENTATION.md); a raised host condition is quotiented (only
   "raises" is claimed, not which condition); KLambda strings are ASCII
   here, as in SchemeWrappers.

   Discovered divergences, proved for every contract-satisfying host:
   - [string_to_n_long]: (string->n S) raises on a string of length >= 2,
     where KLSemantics.rule_string_to_n answers the first code point.
   - [n_to_string_surrogate]: (n->string Z) on a surrogate code 55296..57343
     returns a string whenever SBCL's CODE-CHAR yields a character (SBCL
     characters include the surrogate block, OB-REPR-SBCL-CHARS), where
     rule_n_to_string is a domain error. *)
From Coq Require Import String List Bool Ascii Arith ZArith Lia.
From Buri Require Import CLLowering PortReader Prims2Sources.
From Buri Require KLSyntax KLValue KLSemantics CLWrappers CLContracts SchemeWrappers Native.
Import ListNotations.
Open Scope string_scope.

Module CLStrings.
Module W := CLWrappers.CLWrappers.
Module R := PortReader.PortReader.
Module KV := KLValue.KLValue.
Module KS := KLSemantics.KLSemantics.
Module KY := KLSyntax.KLSyntax.
Notation SL := W.SL.
Notation Sy := W.Sy.

(* ---------- 1. Reviewed ASTs and admission ---------- *)
Definition err msg x := SL [Sy "ERROR"; VStr msg; Sy x].
Definition tlstr_body := SL [Sy "IF";
 SL [Sy "AND"; SL [Sy "STRINGP"; Sy "X"]; SL [Sy "PLUSP"; SL [Sy "LENGTH"; Sy "X"]]];
 SL [Sy "SUBSEQ"; Sy "X"; VNum "1"];
 err "~S is not a non-empty string~%" "X"].
Definition string_to_n_body := SL [Sy "IF";
 SL [Sy "AND"; SL [Sy "STRINGP"; Sy "S"]; SL [Sy "="; VNum "1"; SL [Sy "LENGTH"; Sy "S"]]];
 SL [Sy "CHAR-CODE"; SL [Sy "CHAR"; Sy "S"; VNum "0"]];
 err "~S is not a unit string~%" "S"].
Definition pos_body := SL [Sy "COND";
 SL [SL [Sy "NOT"; SL [Sy "STRINGP"; Sy "X"]]; err "~A is not a string~%" "X"];
 SL [SL [Sy "OR"; SL [Sy "NOT"; SL [Sy "INTEGERP"; Sy "N"]]; SL [Sy "MINUSP"; Sy "N"]; SL [Sy ">="; Sy "N"; SL [Sy "LENGTH"; Sy "X"]]];
     err "~A is not a natural number less than the length of the string~%" "N"];
 SL [Sy "T"; SL [Sy "MAKE-STRING"; VNum "1"; Sy ":INITIAL-ELEMENT"; SL [Sy "CHAR"; Sy "X"; Sy "N"]]]].
Definition n_to_string_body := SL [Sy "LET";
 SL [SL [Sy "C"; SL [Sy "AND"; SL [Sy "INTEGERP"; Sy "N"]; SL [Sy "NOT"; SL [Sy "MINUSP"; Sy "N"]];
                     SL [Sy "<"; Sy "N"; Sy "CHAR-CODE-LIMIT"]; SL [Sy "CODE-CHAR"; Sy "N"]]]];
 SL [Sy "IF"; Sy "C"; SL [Sy "MAKE-STRING"; VNum "1"; Sy ":INITIAL-ELEMENT"; Sy "C"];
     err "~A is not a natural number~%" "N"]].
Definition get_address_body := SL [Sy "SVREF"; Sy "VECTOR"; Sy "N"].
Definition intern_body := SL [Sy "INTERN"; SL [Sy "shen-cl.process-intern"; Sy "STRING"]].

Definition admit_one (src : string) (name : string) (ps : list string) (expected : sv) : bool :=
 match R.read true src with
 | Some [d] => match W.defun_of d with
   | Some (f, (qs, [b])) => (String.eqb f name && (if List.list_eq_dec string_dec qs ps then true else false) && sv_eqb b expected)%bool
   | _ => false end
 | _ => false end.
Theorem cl_strings_admitted :
 admit_one cl_tlstr_source "tlstr" ["X"] tlstr_body = true /\
 admit_one cl_string_to_n_source "string->n" ["S"] string_to_n_body = true /\
 admit_one cl_pos_source "pos" ["X"; "N"] pos_body = true /\
 admit_one cl_n_to_string_source "n->string" ["N"] n_to_string_body = true /\
 admit_one cl_get_address_source "<-address" ["VECTOR"; "N"] get_address_body = true /\
 admit_one cl_intern_source "intern" ["STRING"] intern_body = true.
Proof. vm_compute. repeat split; reflexivity. Qed.

(* ---------- 2. Named host contracts ---------- *)
(* SBCL string and character operations at the shapes the captured bodies
   reach (E2E-21 representations, E2E-24 runtime routines). [chr] is the
   host character of an ASCII character, [cchar] the CODE-CHAR result. *)
Record cl_string_ops (h : string -> list sv -> W.cres) (chr : ascii -> sv) (cchar : Z -> sv) : Prop := {
 str_length : forall s, h "LENGTH" [VStr s] = W.CRet (W.zs (Z.of_nat (String.length s)));
 str_plusp : forall z, h "PLUSP" [W.zs z] = W.CRet (W.hb (Z.gtb z 0));
 str_minusp : forall z, h "MINUSP" [W.zs z] = W.CRet (W.hb (Z.ltb z 0));
 str_ge : forall x y, h ">=" [W.zs x; W.zs y] = W.CRet (W.hb (Z.geb x y));
 str_lt : forall x y, h "<" [W.zs x; W.zs y] = W.CRet (W.hb (Z.ltb x y));
 str_num_eq : forall x y, h "=" [W.zs x; W.zs y] = W.CRet (W.hb (Z.eqb x y));
 str_integerp_int : forall z, h "INTEGERP" [W.zs z] = W.CRet W.T;
 str_subseq_one : forall c s, h "SUBSEQ" [VStr (String c s); W.zs 1] = W.CRet (VStr s);
 str_char : forall s k c, String.get k s = Some c -> h "CHAR" [VStr s; W.zs (Z.of_nat k)] = W.CRet (chr c);
 str_char_code : forall c, h "CHAR-CODE" [chr c] = W.CRet (W.zs (Z.of_nat (nat_of_ascii c)));
 str_make_string : forall c, h "MAKE-STRING" [W.zs 1; VSym ":INITIAL-ELEMENT"; chr c] = W.CRet (VStr (String c EmptyString));
 str_code_char : forall z, (0 <= z < 1114112)%Z -> h "CODE-CHAR" [W.zs z] = W.CRet (cchar z) /\ cchar z <> VNil;
 str_code_char_ascii : forall z, (0 <= z < 256)%Z -> cchar z = chr (ascii_of_nat (Z.to_nat z));
 str_make_string_char : forall z, (0 <= z < 1114112)%Z -> exists r, h "MAKE-STRING" [W.zs 1; VSym ":INITIAL-ELEMENT"; cchar z] = W.CRet r;
 str_error : forall args, exists e, h "ERROR" args = W.CRaise e }.
(* SBCL SVREF on a simple vector [vec xs] under the image's (safety 3)
   proclamation: the element in range, a raised condition otherwise. *)
Record cl_vector_ops (h : string -> list sv -> W.cres) (vec : list sv -> sv) : Prop := {
 vec_svref_in : forall xs k x, nth_error xs k = Some x -> h "SVREF" [vec xs; W.zs (Z.of_nat k)] = W.CRet x;
 vec_svref_out : forall xs z, ~ (0 <= z < Z.of_nat (List.length xs))%Z -> exists e, h "SVREF" [vec xs; W.zs z] = W.CRaise e }.
(* CL INTERN, and the uncaptured |shen-cl.process-intern| (a LOOP body outside
   the evaluated subset): identity on names with none of the escaped
   characters # ' ` |, and a raised type error on a non-string. *)
Fixpoint plain_name (s : string) : bool := match s with
 | EmptyString => true
 | String c r => (negb (Ascii.eqb c "#" || Ascii.eqb c "'" || Ascii.eqb c "`" || Ascii.eqb c "|") && plain_name r)%bool end.
Record cl_intern_ops (h : string -> list sv -> W.cres) : Prop := {
 intern_symbol : forall s, h "INTERN" [VStr s] = W.CRet (VSym s);
 process_plain : forall s, plain_name s = true -> h "shen-cl.process-intern" [VStr s] = W.CRet (VStr s);
 process_nonstring : forall v, is_str v = false -> exists e, h "shen-cl.process-intern" [v] = W.CRaise e }.

(* ---------- 3. Representation of first-order KLambda data ---------- *)
(* Integers by canonical spelling, ASCII strings and symbols by name, the
   Booleans as the symbols true/false (Shen-CL's representation), () as NIL. *)
Inductive rep_c : KV.value -> sv -> Prop :=
 | rc_int z : rep_c (KV.VNum (KY.NInt z)) (W.zs z)
 | rc_str s : rep_c (KV.VStr (KY.of_string s)) (VStr s)
 | rc_sym s : s <> "true" -> s <> "false" -> rep_c (KV.VSym (KY.of_string s)) (VSym s)
 | rc_bool b : rep_c (KV.VBool b) (VSym (if b then "true" else "false"))
 | rc_nil : rep_c KV.VNil VNil
 | rc_cons a a' d d' : rep_c a a' -> rep_c d d' -> rep_c (KV.VCons a d) (VCons a' d').
(* A rule outcome and a CL outcome agree: both return represented values with
   the store unchanged, or the rule throws and the body raises. *)
Definition refines (ks : KV.store) (r : KS.presult) (c : W.cres) : Prop :=
 (exists k v, r = KS.ret k ks /\ rep_c k v /\ c = W.CRet v) \/
 ((exists x, r = KS.throw x) /\ exists e, c = W.CRaise e).
Definition consts : binding := [(":INITIAL-ELEMENT", VSym ":INITIAL-ELEMENT"); ("CHAR-CODE-LIMIT", W.zs 1114112)].
Definition env1 x v : binding := (x, v) :: consts.
Definition env2 x v y w : binding := (x, v) :: (y, w) :: consts.

Lemma of_string_length : forall s, List.length (KY.of_string s) = String.length s.
Proof. induction s; cbn; auto. Qed.
Lemma of_string_nth : forall s k, nth_error (KY.of_string s) k = option_map (fun c => N.of_nat (nat_of_ascii c)) (String.get k s).
Proof. induction s; intros [|k]; cbn; auto. Qed.
Lemma is_num_rep : forall k v, rep_c k v -> is_num v = true -> exists z, k = KV.VNum (KY.NInt z) /\ v = W.zs z.
Proof. intros k v H N; destruct H; cbn in N; try discriminate; eauto. Qed.
Lemma is_str_rep : forall k v, rep_c k v -> is_str v = true -> exists s, k = KV.VStr (KY.of_string s) /\ v = VStr s.
Proof. intros k v H N; destruct H; cbn in N; try discriminate; eauto. Qed.
Lemma zs_num : forall z, is_num (W.zs z) = true.
Proof. reflexivity. Qed.

(* ---------- 4. Evaluation steps ---------- *)
Ltac plain_rw P := let Q := fresh in pose proof (W.plain_split _ P) as Q;
 destruct Q as [Q1 [Q2 [Q3 [Q4 [Q5 [Q6 [Q8 Q7]]]]]]];
 cbn [W.ceval R.to_list W.SL fold_right option_map W.Sy]; rewrite Q1, Q2, Q3, Q4, Q5, Q6, Q8, Q7.
Ltac host := first [eapply W.ce_host2; [reflexivity|reflexivity| | | ] | eapply W.ce_host1; [reflexivity|reflexivity| | ]].
Ltac cvar := apply W.ce_var; reflexivity.

Section Bodies.
Variables (h : string -> list sv -> W.cres) (chr : ascii -> sv) (cchar : Z -> sv) (vec : list sv -> sv).
Hypothesis HH : CLContracts.CLContracts.cl_host_ops h.
Hypothesis SO : cl_string_ops h chr cchar.

Lemma ce_lit : forall m env v, (match v with VNum _ | VStr _ => True | _ => False end) -> W.ceval (S m) h env v = W.CRet v.
Proof. intros m env v H; destruct v; try contradiction; reflexivity. Qed.
Lemma ce_host3 : forall m env g x y z a b c r, W.plain g = true -> W.assoc g W.program = None ->
 W.ceval m h env x = W.CRet a -> W.ceval m h env y = W.CRet b -> W.ceval m h env z = W.CRet c -> h g [a; b; c] = r ->
 W.ceval (S m) h env (SL [Sy g; x; y; z]) = r.
Proof. intros m env g x y z a b c r P A Hx Hy Hz Hr. plain_rw P. rewrite Hx, Hy, Hz, A. exact Hr. Qed.
Lemma ce_or3 : forall m env x y z v, W.ceval m h env x = W.CRet v ->
 W.ceval (S m) h env (SL [Sy "OR"; x; y; z]) = if W.truthy v then W.CRet v else W.ceval (S m) h env (SL [Sy "OR"; y; z]).
Proof. intros; cbn; rewrite H; destruct v; reflexivity. Qed.
Lemma ce_and4 : forall m env x y z w v, W.ceval m h env x = W.CRet v ->
 W.ceval (S m) h env (SL [Sy "AND"; x; y; z; w]) = if W.truthy v then W.ceval (S m) h env (SL [Sy "AND"; y; z; w]) else W.CRet VNil.
Proof. intros; cbn; rewrite H; destruct v; reflexivity. Qed.
Lemma ce_err : forall m env msg x v, String.eqb x "T" = false -> lookup x env = Some v ->
 exists e, W.ceval (S (S m)) h env (err msg x) = W.CRaise e.
Proof.
 intros m env msg x v T L. destruct (str_error _ _ _ SO [VStr msg; v]) as [e E]. exists e.
 eapply W.ce_host2; [reflexivity|reflexivity|reflexivity|apply W.ce_var; eassumption|exact E].
Qed.
Lemma stringp_step : forall m env x v, String.eqb x "T" = false -> lookup x env = Some v ->
 W.ceval (S (S m)) h env (SL [Sy "STRINGP"; Sy x]) = W.CRet (W.hb (is_str v)).
Proof. intros. host; [apply W.ce_var; eassumption|apply (CLContracts.CLContracts.host_stringp h HH)]. Qed.
Lemma integerp_nonnum : forall v, is_num v = false -> h "INTEGERP" [v] = W.CRet VNil.
Proof.
 intros v N. destruct (CLContracts.CLContracts.host_integerp h HH v) as [r [E I]]. rewrite E.
 destruct r; [rewrite (I eq_refl) in N; discriminate|reflexivity].
Qed.

(* ----- tlstr ----- *)
Theorem tlstr_body_spec : forall v n, n >= 6 -> match v with
 | VStr (String c s) => W.ceval n h (env1 "X" v) tlstr_body = W.CRet (VStr s)
 | _ => exists e, W.ceval n h (env1 "X" v) tlstr_body = W.CRaise e end.
Proof.
 intros v n Hn. assert (exists m, n = S (S (S (S (S (S m)))))) as [m ->] by (exists (n - 6); lia).
 unfold tlstr_body.
 destruct (is_str v) eqn:Sv.
 - destruct v; try discriminate.
   rewrite (W.ce_if h _ _ _ _ _ (W.hb (Z.gtb (Z.of_nat (String.length s)) 0))).
   2: { rewrite (W.ce_and2 h _ _ _ _ W.T) by (rewrite (stringp_step _ _ "X" (VStr s)) by reflexivity; reflexivity). cbn [W.truthy W.T].
        host; [host; [cvar|apply (str_length _ _ _ SO)]|apply (str_plusp _ _ _ SO)]. }
   destruct s as [|c s]; cbn [String.length Z.of_nat Z.gtb W.hb W.truthy].
   + apply (ce_err _ _ _ "X" (VStr "")); reflexivity.
   + replace (match Z.compare (Z.pos (Pos.of_succ_nat (String.length s))) 0 with Gt => true | _ => false end) with true by reflexivity.
     cbn [W.hb W.truthy]. host; [cvar|reflexivity|apply (str_subseq_one _ _ _ SO)].
 - rewrite (W.ce_if h _ _ _ _ _ VNil).
   2: { rewrite (W.ce_and2 h _ _ _ _ VNil); [reflexivity|]. rewrite (stringp_step _ _ "X" v) by reflexivity. rewrite Sv; reflexivity. }
   cbn [W.truthy].
   destruct (ce_err (S (S m)) (env1 "X" v) "~S is not a non-empty string~%" "X" v) as [e E]; try reflexivity.
   destruct v; try discriminate; exists e; exact E.
Qed.
(* The captured |tlstr| refines rule_tlstr on every represented argument. *)
Theorem tlstr_refines : forall k v ks n, n >= 6 -> rep_c k v ->
 refines ks (KS.rule_tlstr [k] ks) (W.ceval n h (env1 "X" v) tlstr_body).
Proof.
 intros k v ks n Hn R. pose proof (tlstr_body_spec v n Hn) as B.
 destruct R as [z|s|s T F|b| |a a' d d' _ _].
 - right; split; [eexists; reflexivity|exact B].
 - destruct s as [|c s].
   + right; split; [eexists; reflexivity|exact B].
   + left. exists (KV.VStr (KY.of_string s)), (VStr s). split; [reflexivity|split; [constructor|exact B]].
 - right; split; [eexists; reflexivity|exact B].
 - right; split; [eexists; reflexivity|destruct b; exact B].
 - right; split; [eexists; reflexivity|exact B].
 - right; split; [eexists; reflexivity|exact B].
Qed.

(* ----- string->n ----- *)
Lemma s2n_test : forall m s, W.ceval (S (S (S (S (S m))))) h (env1 "S" (VStr s))
 (SL [Sy "AND"; SL [Sy "STRINGP"; Sy "S"]; SL [Sy "="; VNum "1"; SL [Sy "LENGTH"; Sy "S"]]]) =
 W.CRet (W.hb (Z.eqb 1 (Z.of_nat (String.length s)))).
Proof.
 intros. rewrite (W.ce_and2 h _ _ _ _ W.T) by (rewrite (stringp_step _ _ "S" (VStr s)) by reflexivity; reflexivity).
 cbn [W.truthy W.T]. host; [reflexivity|host; [cvar|apply (str_length _ _ _ SO)]|exact (str_num_eq _ _ _ SO 1 _)].
Qed.
Theorem string_to_n_body_spec : forall v n, n >= 7 -> match v with
 | VStr (String c EmptyString) => W.ceval n h (env1 "S" v) string_to_n_body = W.CRet (W.zs (Z.of_nat (nat_of_ascii c)))
 | _ => exists e, W.ceval n h (env1 "S" v) string_to_n_body = W.CRaise e end.
Proof.
 intros v n Hn. assert (exists m, n = S (S (S (S (S (S (S m))))))) as [m ->] by (exists (n - 7); lia).
 unfold string_to_n_body.
 assert (Er : forall w, (exists e, W.ceval (S (S m)) h (env1 "S" w) (err "~S is not a unit string~%" "S") = W.CRaise e)).
 { intro w; destruct (ce_err m (env1 "S" w) "~S is not a unit string~%" "S" w) as [e E]; try reflexivity. exists e; exact E. }
 destruct (is_str v) eqn:Sv.
 - destruct v; try discriminate.
   rewrite (W.ce_if h _ _ _ _ _ _ (s2n_test (S m) s)).
   destruct s as [|c [|d r]].
   + cbn. destruct (Er (VStr "")) as [e E]; exists e; exact E.
   + cbn [String.length Z.of_nat W.hb Z.eqb Pos.eqb Pos.of_succ_nat W.truthy].
     host; [host; [cvar|reflexivity|apply (str_char _ _ _ SO (String c "") 0 c); reflexivity]|apply (str_char_code _ _ _ SO)].
   + replace (Z.eqb 1 (Z.of_nat (String.length (String c (String d r))))) with false
       by (symmetry; apply Z.eqb_neq; cbn [String.length]; lia).
     cbn [W.hb W.truthy]. apply Er.
 - rewrite (W.ce_if h _ _ _ _ _ VNil).
   2: { rewrite (W.ce_and2 h _ _ _ _ VNil); [reflexivity|]. rewrite (stringp_step _ _ "S" v) by reflexivity. rewrite Sv; reflexivity. }
   cbn [W.truthy]. destruct (Er v) as [e E]. destruct v; try discriminate; exists e; exact E.
Qed.
(* On strings of length <= 1 and on non-strings, |string->n| refines
   rule_string_to_n. *)
Theorem string_to_n_refines : forall k v ks n, n >= 7 -> rep_c k v ->
 (forall s, v = VStr s -> String.length s <= 1) ->
 refines ks (KS.rule_string_to_n [k] ks) (W.ceval n h (env1 "S" v) string_to_n_body).
Proof.
 intros k v ks n Hn R L. pose proof (string_to_n_body_spec v n Hn) as B.
 destruct R as [z|s|s T F|b| |a a' d d' _ _].
 - right; split; [eexists; reflexivity|exact B].
 - destruct s as [|c [|d r]].
   + right; split; [eexists; reflexivity|exact B].
   + left. exists (KV.VNum (KY.NInt (Z.of_nat (nat_of_ascii c)))), (W.zs (Z.of_nat (nat_of_ascii c))).
     split; [|split; [constructor|exact B]].
     cbn. rewrite nat_N_Z. reflexivity.
   + specialize (L _ eq_refl). cbn in L. lia.
 - right; split; [eexists; reflexivity|exact B].
 - right; split; [eexists; reflexivity|destruct b; exact B].
 - right; split; [eexists; reflexivity|exact B].
 - right; split; [eexists; reflexivity|exact B].
Qed.
(* Discovered divergence: on every string of length >= 2 the captured body
   raises, while rule_string_to_n returns the first code point. *)
Theorem string_to_n_long : forall c d r ks n, n >= 7 ->
 KS.rule_string_to_n [KV.VStr (KY.of_string (String c (String d r)))] ks =
   KS.ret (KV.VNum (KY.NInt (Z.of_nat (nat_of_ascii c)))) ks /\
 exists e, W.ceval n h (env1 "S" (VStr (String c (String d r)))) string_to_n_body = W.CRaise e.
Proof.
 intros c d r ks n Hn. split; [cbn; rewrite nat_N_Z; reflexivity|].
 exact (string_to_n_body_spec (VStr (String c (String d r))) n Hn).
Qed.

(* ----- pos ----- *)
Lemma get_some : forall s k, k < String.length s -> exists c, String.get k s = Some c.
Proof. induction s as [|c s IH]; intros [|k] L; cbn in *; try lia; eauto. apply IH; lia. Qed.
Definition pos_or := SL [Sy "OR"; SL [Sy "NOT"; SL [Sy "INTEGERP"; Sy "N"]]; SL [Sy "MINUSP"; Sy "N"]; SL [Sy ">="; Sy "N"; SL [Sy "LENGTH"; Sy "X"]]].
Lemma pos_or_int : forall m s z, W.ceval (S (S (S (S m)))) h (env2 "X" (VStr s) "N" (W.zs z)) pos_or =
 W.CRet (W.hb (Z.ltb z 0 || Z.geb z (Z.of_nat (String.length s)))).
Proof.
 intros. unfold pos_or. rewrite (ce_or3 _ _ _ _ _ VNil).
 2: { host; [host; [cvar|apply (str_integerp_int _ _ _ SO)]|apply (CLContracts.CLContracts.host_not h HH)]. }
 cbn [W.truthy]. rewrite (W.ce_or2 h _ _ _ _ (W.hb (Z.ltb z 0))) by (host; [cvar|apply (str_minusp _ _ _ SO)]).
 destruct (Z.ltb z 0); cbn [W.hb W.truthy orb]; [reflexivity|].
 host; [cvar|host; [cvar|apply (str_length _ _ _ SO)]|apply (str_ge _ _ _ SO)].
Qed.
Lemma pos_or_nonint : forall m s w, is_num w = false -> W.ceval (S (S (S (S m)))) h (env2 "X" (VStr s) "N" w) pos_or = W.CRet W.T.
Proof.
 intros m s w N. unfold pos_or. rewrite (ce_or3 _ _ _ _ _ W.T); [reflexivity|].
 host; [host; [cvar|apply (integerp_nonnum _ N)]|apply (CLContracts.CLContracts.host_not h HH)].
Qed.
Lemma not_stringp : forall m env x v, String.eqb x "T" = false -> lookup x env = Some v ->
 W.ceval (S (S (S m))) h env (SL [Sy "NOT"; SL [Sy "STRINGP"; Sy x]]) = W.CRet (W.hb (negb (is_str v))).
Proof.
 intros. host; [apply stringp_step; eassumption|]. rewrite (CLContracts.CLContracts.host_not h HH). destruct (is_str v); reflexivity.
Qed.
Theorem pos_refines : forall k1 v1 k2 v2 ks n, n >= 6 -> rep_c k1 v1 -> rep_c k2 v2 ->
 refines ks (KS.rule_pos [k1; k2] ks) (W.ceval n h (env2 "X" v1 "N" v2) pos_body).
Proof.
 intros k1 v1 k2 v2 ks n Hn R1 R2. assert (exists m, n = S (S (S (S (S (S m)))))) as [m ->] by (exists (n - 6); lia).
 unfold pos_body.
 assert (Er : forall msg x w, lookup x (env2 "X" v1 "N" v2) = Some w -> String.eqb x "T" = false ->
   exists e, W.ceval (S (S (S (S m)))) h (env2 "X" v1 "N" v2) (err msg x) = W.CRaise e).
 { intros msg x w L T. apply (ce_err _ _ _ _ w T L). }
 destruct (is_str v1) eqn:S1.
 - destruct (is_str_rep _ _ R1 S1) as [s [-> ->]].
   rewrite (W.ce_cond_miss h _ _ _ _ _) by (rewrite (not_stringp _ _ "X" (VStr s)) by reflexivity; reflexivity).
   destruct (is_num v2) eqn:N2.
   + destruct (is_num_rep _ _ R2 N2) as [z [-> ->]].
     destruct (Z.ltb z 0 || Z.geb z (Z.of_nat (String.length s)))%bool eqn:B.
     * rewrite (W.ce_cond_hit h _ _ _ _ _ W.T); [| |reflexivity].
       2: { rewrite pos_or_int, B. reflexivity. }
       right. split.
       -- eexists. unfold KS.rule_pos. rewrite of_string_length.
          destruct (Z.leb 0 z) eqn:Z0; destruct (Z.ltb z (Z.of_nat (String.length s))) eqn:Z1; cbn [andb]; try reflexivity.
          exfalso. apply orb_true_iff in B as [B|B]; [apply Z.ltb_lt in B; apply Z.leb_le in Z0|apply Z.geb_le in B; apply Z.ltb_lt in Z1]; lia.
       -- apply (Er _ "N" (W.zs z)); reflexivity.
     * pose proof B as Bc. apply orb_false_iff in B as [B0 B1]. apply Z.ltb_ge in B0.
       assert (B1' : (z < Z.of_nat (String.length s))%Z) by (destruct (Z.geb_spec z (Z.of_nat (String.length s))) as [G|G]; [discriminate|lia]).
       destruct (Z_of_nat_complete z B0) as [k ->].
       assert (Lk : k < String.length s) by lia. destruct (get_some s k Lk) as [c Gc].
       rewrite (W.ce_cond_miss h _ _ _ _ _) by (rewrite pos_or_int, Bc; reflexivity).
       rewrite (W.ce_cond_hit h _ _ _ _ _ W.T) by reflexivity.
       left. exists (KV.VStr [N.of_nat (nat_of_ascii c)]), (VStr (String c EmptyString)). split; [|split].
       -- unfold KS.rule_pos. rewrite of_string_length, Nat2Z.id, of_string_nth, Gc.
          replace (Z.leb 0 (Z.of_nat k) && Z.ltb (Z.of_nat k) (Z.of_nat (String.length s)))%bool with true; [reflexivity|].
          symmetry. apply andb_true_iff. split; [apply Z.leb_le|apply Z.ltb_lt]; lia.
       -- exact (rc_str (String c EmptyString)).
       -- apply (ce_host3 _ _ _ _ _ _ (W.zs 1) (VSym ":INITIAL-ELEMENT") (chr c)); try reflexivity.
          ++ host; [cvar|cvar|apply (str_char _ _ _ SO); exact Gc].
          ++ apply (str_make_string _ _ _ SO).
   + rewrite (W.ce_cond_hit h _ _ _ _ _ W.T) by (first [reflexivity | apply pos_or_nonint; exact N2]).
     right. split.
     * destruct R2; cbn in N2; try discriminate; eexists; reflexivity.
     * apply (Er _ "N" v2); reflexivity.
 - rewrite (W.ce_cond_hit h _ _ _ _ _ W.T).
   2: { rewrite (not_stringp _ _ "X" v1) by reflexivity. rewrite S1. reflexivity. }
   2: reflexivity.
   right. split.
   + destruct R1; cbn in S1; try discriminate; eexists; reflexivity.
   + apply (Er _ "X" v1); reflexivity.
Qed.

(* ----- n->string ----- *)
Definition nts_and := SL [Sy "AND"; SL [Sy "INTEGERP"; Sy "N"]; SL [Sy "NOT"; SL [Sy "MINUSP"; Sy "N"]];
 SL [Sy "<"; Sy "N"; Sy "CHAR-CODE-LIMIT"]; SL [Sy "CODE-CHAR"; Sy "N"]].
Definition in_range z := (Z.leb 0 z && Z.ltb z 1114112)%bool.
Lemma nts_and_int : forall m z, W.ceval (S (S (S (S (S m))))) h (env1 "N" (W.zs z)) nts_and =
 W.CRet (if in_range z then cchar z else VNil).
Proof.
 intros. unfold nts_and, in_range. rewrite (ce_and4 _ _ _ _ _ _ W.T) by (host; [cvar|apply (str_integerp_int _ _ _ SO)]).
 cbn [W.truthy W.T]. rewrite (W.ce_and3 h _ _ _ _ _ (W.hb (negb (Z.ltb z 0)))).
 2: { host; [host; [cvar|apply (str_minusp _ _ _ SO)]|]. rewrite (CLContracts.CLContracts.host_not h HH). destruct (Z.ltb z 0); reflexivity. }
 destruct (Z.ltb z 0) eqn:L; cbn [negb W.hb W.truthy].
 - replace (Z.leb 0 z) with false by (symmetry; apply Z.leb_gt; apply Z.ltb_lt in L; exact L). reflexivity.
 - replace (Z.leb 0 z) with true by (symmetry; apply Z.leb_le; apply Z.ltb_ge in L; exact L). cbn [andb].
   rewrite (W.ce_and2 h _ _ _ _ (W.hb (Z.ltb z 1114112))) by (host; [cvar|cvar|apply (str_lt _ _ _ SO)]).
   destruct (Z.ltb z 1114112) eqn:L2; cbn [W.hb W.truthy]; [|reflexivity].
   host; [cvar|]. apply (str_code_char _ _ _ SO). apply Z.ltb_ge in L; apply Z.ltb_lt in L2; lia.
Qed.
Theorem n_to_string_int : forall z n, n >= 8 ->
 if in_range z then exists r, W.ceval n h (env1 "N" (W.zs z)) n_to_string_body = W.CRet r /\
   ((z < 256)%Z -> r = VStr (String (ascii_of_nat (Z.to_nat z)) EmptyString))
 else exists e, W.ceval n h (env1 "N" (W.zs z)) n_to_string_body = W.CRaise e.
Proof.
 intros z n Hn. assert (exists m, n = S (S (S (S (S (S (S (S m)))))))) as [m ->] by (exists (n - 8); lia).
 unfold n_to_string_body. rewrite (W.ce_let h _ _ _ _ _ _ (nts_and_int _ z)).
 destruct (in_range z) eqn:B.
 - assert (Rz : (0 <= z < 1114112)%Z) by (unfold in_range in B; apply andb_true_iff in B as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2; lia).
   destruct (str_code_char _ _ _ SO z Rz) as [_ NZ]. destruct (str_make_string_char _ _ _ SO z Rz) as [r Er].
   rewrite (W.ce_if h _ _ _ _ _ (cchar z)) by cvar.
   replace (W.truthy (cchar z)) with true by (destruct (cchar z); try reflexivity; contradiction).
   exists r. split.
   + apply (ce_host3 _ _ _ _ _ _ (W.zs 1) (VSym ":INITIAL-ELEMENT") (cchar z)); try reflexivity; try cvar. exact Er.
   + intro L. rewrite (str_code_char_ascii _ _ _ SO z) in Er by lia. rewrite (str_make_string _ _ _ SO) in Er.
     injection Er; auto.
 - rewrite (W.ce_if h _ _ _ _ _ VNil) by cvar. cbn [W.truthy].
   apply (ce_err _ _ _ "N" (W.zs z)); reflexivity.
Qed.
Theorem n_to_string_nonnum : forall v n, n >= 8 -> is_num v = false ->
 exists e, W.ceval n h (env1 "N" v) n_to_string_body = W.CRaise e.
Proof.
 intros v n Hn N. assert (exists m, n = S (S (S (S (S (S (S (S m)))))))) as [m ->] by (exists (n - 8); lia).
 unfold n_to_string_body. rewrite (W.ce_let h _ _ _ _ _ (W.CRet VNil)).
 2: { unfold nts_and. rewrite (ce_and4 _ _ _ _ _ _ VNil) by (host; [cvar|apply (integerp_nonnum _ N)]). reflexivity. }
 rewrite (W.ce_if h _ _ _ _ _ VNil) by cvar. cbn [W.truthy].
 apply (ce_err _ _ _ "N" v); reflexivity.
Qed.
Lemma scalar_ok_iff : forall z, KV.scalar_ok z = true <-> (0 <= z <= 1114111 /\ ~ (55296 <= z <= 57343))%Z.
Proof.
 intro z. unfold KV.scalar_ok.
 destruct (Z.leb_spec 0 z), (Z.leb_spec z 1114111), (Z.leb_spec 55296 z), (Z.leb_spec z 57343);
 cbn; split; intro Hs; try discriminate; try reflexivity; try lia.
Qed.
(* |n->string| refines rule_n_to_string on every represented argument other
   than an in-range code point >= 256 (whose host string lies outside this
   module's ASCII string model; see n_to_string_scalar). *)
Theorem n_to_string_refines : forall k v ks n, n >= 8 -> rep_c k v ->
 (forall z, k = KV.VNum (KY.NInt z) -> (z < 256)%Z \/ ~ (0 <= z < 1114112)%Z) ->
 refines ks (KS.rule_n_to_string [k] ks) (W.ceval n h (env1 "N" v) n_to_string_body).
Proof.
 intros k v ks n Hn R Hk. destruct R as [z|s|s T F|b| |a a' d d' _ _].
 - pose proof (n_to_string_int z n Hn) as B. specialize (Hk z eq_refl).
   destruct (in_range z) eqn:IR.
   + assert (Rz : (0 <= z < 1114112)%Z) by (unfold in_range in IR; apply andb_true_iff in IR as [B1 B2]; apply Z.leb_le in B1; apply Z.ltb_lt in B2; lia).
     destruct Hk as [L|L]; [|contradiction].
     destruct B as [r [Er Ar]]. specialize (Ar L). subst r.
     left. exists (KV.VStr [Z.to_N z]), (VStr (String (ascii_of_nat (Z.to_nat z)) EmptyString)). split; [|split; [|exact Er]].
     * unfold KS.rule_n_to_string. replace (KV.scalar_ok z) with true by (symmetry; apply scalar_ok_iff; lia). reflexivity.
     * replace [Z.to_N z] with (KY.of_string (String (ascii_of_nat (Z.to_nat z)) EmptyString)); [constructor|].
       cbn. rewrite nat_ascii_embedding by lia. rewrite Z_nat_N. reflexivity.
   + right. split; [|exact B].
     unfold KS.rule_n_to_string. replace (KV.scalar_ok z) with false; [eexists; reflexivity|].
     symmetry. destruct (KV.scalar_ok z) eqn:E; [|reflexivity]. apply scalar_ok_iff in E.
     unfold in_range in IR. destruct (Z.leb_spec 0 z), (Z.ltb_spec z 1114112); cbn in IR; try discriminate; lia.
 - right; split; [eexists; reflexivity|apply n_to_string_nonnum; auto].
 - right; split; [eexists; reflexivity|apply n_to_string_nonnum; auto].
 - right; split; [eexists; reflexivity|apply n_to_string_nonnum; [auto|destruct b; reflexivity]].
 - right; split; [eexists; reflexivity|apply n_to_string_nonnum; auto].
 - right; split; [eexists; reflexivity|apply n_to_string_nonnum; auto].
Qed.
(* Every scalar value is accepted by both: the rule returns the one-character
   string and the body returns without raising. *)
Theorem n_to_string_scalar : forall z ks n, n >= 8 -> KV.scalar_ok z = true ->
 KS.rule_n_to_string [KV.VNum (KY.NInt z)] ks = KS.ret (KV.VStr [Z.to_N z]) ks /\
 exists r, W.ceval n h (env1 "N" (W.zs z)) n_to_string_body = W.CRet r.
Proof.
 intros z ks n Hn Sz. split; [unfold KS.rule_n_to_string; rewrite Sz; reflexivity|].
 pose proof (n_to_string_int z n Hn) as B. apply scalar_ok_iff in Sz.
 replace (in_range z) with true in B by (symmetry; unfold in_range; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
 destruct B as [r [E _]]; eauto.
Qed.
(* Discovered divergence: on a surrogate code the rule is a domain error and
   the captured body returns (SBCL's CODE-CHAR yields a character there). *)
Theorem n_to_string_surrogate : forall z ks n, n >= 8 -> (55296 <= z <= 57343)%Z ->
 (exists x, KS.rule_n_to_string [KV.VNum (KY.NInt z)] ks = KS.throw x) /\
 exists r, W.ceval n h (env1 "N" (W.zs z)) n_to_string_body = W.CRet r.
Proof.
 intros z ks n Hn Rz. split.
 - unfold KS.rule_n_to_string. replace (KV.scalar_ok z) with false; [eexists; reflexivity|].
   symmetry. destruct (KV.scalar_ok z) eqn:E; [apply scalar_ok_iff in E; lia|reflexivity].
 - pose proof (n_to_string_int z n Hn) as B.
   replace (in_range z) with true in B by (symmetry; unfold in_range; apply andb_true_iff; split; [apply Z.leb_le|apply Z.ltb_lt]; lia).
   destruct B as [r [E _]]; eauto.
Qed.

(* ----- <-address ----- *)
Theorem get_address_svref : forall v w n, n >= 3 ->
 W.ceval n h (env2 "VECTOR" v "N" w) get_address_body = h "SVREF" [v; w].
Proof.
 intros v w n Hn. assert (exists m, n = S (S (S m))) as [m ->] by (exists (n - 3); lia).
 host; [cvar|cvar|reflexivity].
Qed.
Lemma forall2_nth : forall (A B : Type) (P : A -> B -> Prop) xs ys k x, Forall2 P xs ys -> nth_error xs k = Some x ->
 exists y, nth_error ys k = Some y /\ P x y.
Proof. intros A B P xs ys k x F; revert k; induction F; intros [|k] E; cbn in *; try discriminate; [injection E as ->; eauto|eauto]. Qed.
Section Vector.
Hypothesis VO : cl_vector_ops h vec.
(* The captured |<-address| refines rule_address_get for every heap vector
   whose cells are represented element-wise by the host simple vector, and
   every integer index: the element in range, a raise (XBounds) otherwise.
   The heap-location-to-host-vector correspondence is the premise
   (owned by E2E-21). *)
Theorem get_address_refines : forall l cells xs z ks n, n >= 3 ->
 nth_error (KV.heap ks) l = Some cells -> Forall2 rep_c cells xs ->
 refines ks (KS.rule_address_get [KV.VVec l; KV.VNum (KY.NInt z)] ks)
   (W.ceval n h (env2 "VECTOR" (vec xs) "N" (W.zs z)) get_address_body).
Proof.
 intros l cells xs z ks n Hn Hl F. rewrite get_address_svref by exact Hn.
 unfold KS.rule_address_get. rewrite Hl.
 assert (Out : ~ (0 <= z < Z.of_nat (List.length xs))%Z -> (exists x, KS.throw KV.XBounds = KS.throw x) /\ exists e, h "SVREF" [vec xs; W.zs z] = W.CRaise e).
 { intro O. split; [eauto|apply (vec_svref_out _ _ VO); exact O]. }
 destruct (Z.leb_spec 0 z) as [Z0|Z0].
 - destruct (nth_error cells (Z.to_nat z)) as [c|] eqn:Nc.
   + destruct (forall2_nth _ _ _ _ _ _ _ F Nc) as [x [Nx Rx]].
     left. exists c, x. split; [reflexivity|split; [exact Rx|]].
     replace (W.zs z) with (W.zs (Z.of_nat (Z.to_nat z))) by (rewrite Z2Nat.id by exact Z0; reflexivity). apply (vec_svref_in _ _ VO); exact Nx.
   + right. apply Out. apply nth_error_None in Nc. rewrite (Forall2_length F) in Nc. lia.
 - right. apply Out. lia.
Qed.
End Vector.

(* ----- intern ----- *)
Section Intern.
Hypothesis IO : cl_intern_ops h.
Theorem intern_body_plain : forall s n, n >= 4 -> plain_name s = true ->
 W.ceval n h (env1 "STRING" (VStr s)) intern_body = W.CRet (VSym s).
Proof.
 intros s n Hn P. assert (exists m, n = S (S (S (S m)))) as [m ->] by (exists (n - 4); lia).
 host; [host; [cvar|apply (process_plain _ IO); exact P]|apply (intern_symbol _ IO)].
Qed.
Lemma raise1 : forall m env g x e, W.plain g = true -> W.ceval m h env x = W.CRaise e ->
 W.ceval (S m) h env (SL [Sy g; x]) = W.CRaise e.
Proof. intros m env g x e P Hx. plain_rw P. rewrite Hx. reflexivity. Qed.
(* |intern| refines rule_intern on every represented argument whose name has
   none of the characters # ' ` | (the names the uncaptured
   shen-cl.process-intern leaves unchanged). "true" and "false" give the
   symbols true/false, which represent the Booleans. *)
Theorem intern_refines : forall k v ks n, n >= 4 -> rep_c k v ->
 (forall s, v = VStr s -> plain_name s = true) ->
 refines ks (KS.rule_intern [k] ks) (W.ceval n h (env1 "STRING" v) intern_body).
Proof.
 intros k v ks n Hn R P. assert (exists m, n = S (S (S (S m)))) as [m ->] by (exists (n - 4); lia).
 assert (NS : is_str v = false -> exists e, W.ceval (S (S (S (S m)))) h (env1 "STRING" v) intern_body = W.CRaise e).
 { intro N. destruct (process_nonstring _ IO v N) as [e E]. exists e. apply raise1; [reflexivity|].
   host; [cvar|exact E]. }
 destruct R as [z|s|s T F|b| |a a' d d' _ _].
 - right; split; [eexists; reflexivity|apply NS; reflexivity].
 - left. rewrite intern_body_plain by (auto; lia).
   unfold KS.rule_intern, KS.kw. rewrite !SchemeWrappers.SchemeWrappers.text_of.
   destruct (String.eqb s "true") eqn:T; [apply String.eqb_eq in T; subst s; do 2 eexists; split; [reflexivity|split; [exact (rc_bool true)|reflexivity]]|].
   destruct (String.eqb s "false") eqn:F; [apply String.eqb_eq in F; subst s; do 2 eexists; split; [reflexivity|split; [exact (rc_bool false)|reflexivity]]|].
   apply String.eqb_neq in T, F. do 2 eexists; split; [reflexivity|split; [apply rc_sym; assumption|reflexivity]].
 - right; split; [eexists; reflexivity|apply NS; reflexivity].
 - right; split; [eexists; reflexivity|apply NS; destruct b; reflexivity].
 - right; split; [eexists; reflexivity|apply NS; reflexivity].
 - right; split; [eexists; reflexivity|apply NS; reflexivity].
Qed.
End Intern.
End Bodies.

(* ---------- 5. Anti-vacuity ---------- *)
(* One concrete table satisfies cl_host_ops and the three new records at
   once (integers read back from their spellings, characters as tagged
   one-character strings, vectors as tagged lists). It is not a model of
   SBCL. *)
Definition mchr (c : ascii) : sv := VCons (VSym "CHAR") (VStr (String c EmptyString)).
Definition mcchar (z : Z) : sv := mchr (ascii_of_nat (Z.to_nat z)).
Definition mvec (xs : list sv) : sv := VCons (VSym "VEC") (SL xs).
Definition zop (f : Z -> W.cres) (t : string) : W.cres := match W.zinv t with Some z => f z | None => W.CUnsup end.
Definition model_strings (f : string) (vs : list sv) : W.cres :=
 match f, vs with
 | "LENGTH", [VStr s] => W.CRet (W.zs (Z.of_nat (String.length s)))
 | "PLUSP", [VNum t] => zop (fun z => W.CRet (W.hb (Z.gtb z 0))) t
 | "MINUSP", [VNum t] => zop (fun z => W.CRet (W.hb (Z.ltb z 0))) t
 | ">=", [VNum t; VNum u] => zop (fun x => zop (fun y => W.CRet (W.hb (Z.geb x y))) u) t
 | "<", [VNum t; VNum u] => zop (fun x => zop (fun y => W.CRet (W.hb (Z.ltb x y))) u) t
 | "SUBSEQ", [VStr (String _ s); VNum "1"] => W.CRet (VStr s)
 | "CHAR", [VStr s; VNum t] => zop (fun z => match String.get (Z.to_nat z) s with Some c => W.CRet (mchr c) | None => W.CUnsup end) t
 | "CHAR-CODE", [VCons (VSym "CHAR") (VStr (String c EmptyString))] => W.CRet (W.zs (Z.of_nat (nat_of_ascii c)))
 | "MAKE-STRING", [_; _; VCons (VSym "CHAR") (VStr t)] => W.CRet (VStr t)
 | "CODE-CHAR", [VNum t] => zop (fun z => W.CRet (mcchar z)) t
 | "ERROR", _ => W.CRaise VNil
 | "SVREF", [VCons (VSym "VEC") l; VNum t] => match R.to_list l with
   | Some xs => zop (fun z => if Z.leb 0 z then match nth_error xs (Z.to_nat z) with Some x => W.CRet x | None => W.CRaise VNil end else W.CRaise VNil) t
   | None => W.CUnsup end
 | "INTERN", [VStr s] => W.CRet (VSym s)
 | "shen-cl.process-intern", [VStr s] => W.CRet (VStr s)
 | "shen-cl.process-intern", [_] => W.CRaise VNil
 | _, _ => CLContracts.CLContracts.model_host f vs end.
Lemma zop_zs : forall f z, zop f (Native.Native.spelling z) = f z.
Proof. intros; unfold zop; rewrite W.zinv_zs; reflexivity. Qed.
Theorem model_strings_ops : CLContracts.CLContracts.cl_host_ops model_strings /\
 cl_string_ops model_strings mchr mcchar /\ cl_vector_ops model_strings mvec /\ cl_intern_ops model_strings.
Proof.
 pose proof CLContracts.CLContracts.model_host_ops as M.
 split; [destruct M; constructor; assumption|]. split; [|split].
 - constructor; intros; cbn [model_strings W.zs]; rewrite ?zop_zs; try reflexivity.
   + destruct (Z.eqb_spec x y) as [->|D].
     * cbn. rewrite String.eqb_refl. reflexivity.
     * cbn. destruct (String.eqb_spec (Native.Native.spelling x) (Native.Native.spelling y)) as [E|E]; [apply W.spelling_inj in E; contradiction|reflexivity].
   + rewrite Nat2Z.id, H. reflexivity.
   + split; [reflexivity|discriminate].
   + exists (VStr (String (ascii_of_nat (Z.to_nat z)) EmptyString)). reflexivity.
   + exists VNil. destruct args as [|a [|b r]]; reflexivity.
 - constructor; intros; cbn [model_strings W.zs mvec]; rewrite W.to_list_SL, ?zop_zs.
   + replace (Z.leb 0 (Z.of_nat k)) with true by (symmetry; apply Z.leb_le; lia). rewrite Nat2Z.id, H. reflexivity.
   + exists VNil. destruct (Z.leb_spec 0 z); [|reflexivity].
     destruct (nth_error xs (Z.to_nat z)) eqn:E; [|reflexivity].
     exfalso. apply H. split; [lia|]. assert (Z.to_nat z < List.length xs) by (apply nth_error_Some; congruence). lia.
 - constructor; intros; try reflexivity.
   exists VNil. destruct v; try discriminate; reflexivity.
Qed.
End CLStrings.
