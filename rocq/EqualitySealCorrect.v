(* The actual Shen capsule builder supplies exactly the proved private table.
   Native activation still rests on the named Chez eval/environment contract. *)
From Coq Require Import List String ZArith Bool Arith Lia.
From Buri Require Import Native NativeHelpers NativeRuntime NativeSimulation EqualityCoreInput
 EqualityCoreCorrect EqualityAdmission EqualitySealInput ObserverEffects Equality.
Import ListNotations Native.Native.
Module EqualitySealCorrect.
Module C := EqualityCoreCorrect.EqualityCoreCorrect.
Module A := EqualityAdmission.EqualityAdmission.
Open Scope string_scope.
Definition helper_binding := L [Symbol "kl:=";L [Symbol "lambda";L [Symbol "x";Symbol "y"];
 L [Symbol "equal?";Symbol "x";Symbol "y"]]].
Definition native_def name args body := L [Symbol "define";Pair name args;body].
Definition binding name args body := L [name;L [Symbol "lambda";args;body]].
Definition record source name args body := L [source;native_def name args body].
Theorem captured_definition : forall name args body,
 run 100 equality_seal_program "kl:buri.eq2-seal-definition" [native_def name args body]=Returned (binding name args body).
Proof. intros;vm_compute;reflexivity. Qed.
Theorem captured_four_definition_program : forall sa sb sc sd na nb nc nd aa ab ac ad ba bb bc bd,
 run 100 equality_seal_program "kl:buri.eq2-seal-program"
 [L [record sa na aa ba;record sb nb ab bb;record sc nc ac bc;record sd nd ad bd]]=
 Returned (L [Symbol "letrec";L [helper_binding;binding na aa ba;binding nb ab bb;binding nc ac bc;binding nd ad bd];
 Symbol "kl:buri.eq2-derive"]).
Proof. intros;vm_compute;reflexivity. Qed.
Definition imports := ["lambda";"let";"let*";"letrec";"if";"cond";"and";"or";"quote";
 "eq?";"equal?";"null?";"pair?";"car";"cdr";"cons";"list"].
Definition request program := L [Symbol "eval";L [Symbol "quote";program];
 L [Symbol "environment";L [Symbol "quote";L (Symbol "only"::L [Symbol "chezscheme"]::map Symbol imports)]]].
Theorem captured_authority_request : forall program,
 run 100 equality_seal_program "kl:buri.eq2-seal-request" [program]=Returned (request program).
Proof. intro;vm_compute;reflexivity. Qed.
Theorem no_io_or_eval_authority :
 existsb (String.eqb "eval") imports=false /\ existsb (String.eqb "set!") imports=false /\
 existsb (String.eqb "open-input-file") imports=false /\ existsb (String.eqb "load") imports=false.
Proof. vm_compute;repeat split;reflexivity. Qed.
Local Transparent equality_core_nodes equality_core_text.
Definition targets := Eval vm_compute in match equality_core_nodes with Some xs=>xs|None=>[] end.
Local Opaque equality_core_nodes equality_core_text.
Definition target_binding target := match elements target with
 | Some [Symbol "define";Pair name args;body]=>binding name args body | _=>Nil end.
Definition records := L (map (fun target=>L [Nil;target]) targets).
Definition capsule := L [Symbol "letrec";L (helper_binding::map target_binding targets);Symbol "kl:buri.eq2-derive"].
Definition capsule_definitions := Eval vm_compute in match
 NativeHelpers.helper_definitions (helper_binding::map target_binding targets) with Some ds=>ds|None=>[] end.
Theorem captured_capsule_assembly :
 run 100 equality_seal_program "kl:buri.eq2-seal-program" [records]=Returned capsule.
Proof. vm_compute;reflexivity. Qed.
Theorem capsule_table_exact : capsule_definitions =
 ("kl:=",Def ["x";"y"] (Call "equal?" [Var "x";Var "y"]))::equality_core_program.
Proof. vm_compute;reflexivity. Qed.
Theorem minimal_helper_exact : C.helpers=[("kl:=",Def ["x";"y"] (Call "equal?" [Var "x";Var "y"]))].
Proof. vm_compute;reflexivity. Qed.
Lemma lookup_append : forall ds es name, lookup (ds++es) name=
 match lookup ds name with Some d=>Some d|None=>lookup es name end.
Proof. induction ds as [|[n d] ds IH];intros;[reflexivity|]. cbn [lookup app];destruct (String.eqb name n);[reflexivity|apply IH]. Qed.
Theorem capsule_lookup_agrees : forall name, lookup capsule_definitions name=lookup C.program name.
Proof.
 intro name;rewrite capsule_table_exact;unfold C.program;rewrite minimal_helper_exact,lookup_append.
 cbn [lookup]. destruct (String.eqb name "kl:=") eqn:E.
 - apply String.eqb_eq in E;subst name;vm_compute;reflexivity.
 - destruct (lookup equality_core_program name);[reflexivity|cbn [lookup];try rewrite E;reflexivity].
Qed.
Lemma runtime_apply_congruence : forall p q,
 (forall name,p name=q name) -> forall name vs k,NativeRuntime.apply p name vs k=NativeRuntime.apply q name vs k.
Proof. intros;unfold NativeRuntime.apply;rewrite H;reflexivity. Qed.
Lemma step_program_congruence : forall p q,
 (forall name,p name=q name) -> forall machine,NativeRuntime.step p machine=NativeRuntime.step q machine.
Proof.
 intros p q H [c k];destruct c.
 - destruct e;try reflexivity;destruct args;cbn [NativeRuntime.step];try reflexivity.
   rewrite (runtime_apply_congruence p q H);reflexivity.
 - destruct k as [|f k];[reflexivity|];destruct f;try reflexivity;destruct remaining;
   cbn [NativeRuntime.step];try reflexivity;rewrite (runtime_apply_congruence p q H);reflexivity.
 - reflexivity.
Qed.
Theorem execute_program_congruence : forall fuel p q,
 (forall name,p name=q name) -> forall machine,NativeRuntime.execute fuel p machine=NativeRuntime.execute fuel q machine.
Proof.
 induction fuel as [|fuel IH];intros p q H [c k];destruct c;destruct k;
 cbn [NativeRuntime.execute];try reflexivity.
 all: rewrite (step_program_congruence p q H).
 all: destruct (NativeRuntime.step q _);[apply IH;exact H|reflexivity].
Qed.
Theorem sealed_invocation_agrees : forall steps args,
 NativeRuntime.invoke steps capsule_definitions "kl:buri.eq2-derive" args=
 NativeRuntime.invoke steps C.program "kl:buri.eq2-derive" args.
Proof.
 intros;unfold NativeRuntime.invoke;rewrite capsule_lookup_agrees.
 destruct (lookup C.program "kl:buri.eq2-derive");[destruct (Nat.eqb _ _)|];try reflexivity.
 apply execute_program_congruence;apply capsule_lookup_agrees.
Qed.
Theorem sealed_checker_sound : forall (D:Type) (constants:nat->D) (application:D->D->D) fuel raw p steps a b,
 A.read_certificate fuel raw=Some p ->
 NativeRuntime.invoke steps capsule_definitions "kl:buri.eq2-derive" [raw]=Returned (C.result_value (Some (a,b))) ->
 forall rho,@Equality.denote D constants application rho a=@Equality.denote D constants application rho b.
Proof. intros;rewrite sealed_invocation_agrees in H0;eapply A.admitted_native_checker_sound;eauto. Qed.
Definition activation_operation activate name args : ObserverEffects.computation := fun previous=>
 match name,args with
 | "eval",[req]=>ObserverEffects.Out (activate req) previous [ObserverEffects.Activate req (activate req)]
 | _,_=>ObserverEffects.Out (external name args) previous [] end.
Theorem captured_native_activation : forall activate previous,
 (match lookup equality_seal_program "kl:buri.make-sealed-eq2" with
 | Some d=>ObserverEffects.eval_with 100 (lookup equality_seal_program) (activation_operation activate)
 (arguments (params d) [records]) (body d) previous
 | None=>ObserverEffects.Out Unsupported previous [] end)=
 ObserverEffects.Out (activate (request capsule)) previous [ObserverEffects.Activate (request capsule) (activate (request capsule))].
Proof. intros;vm_compute;reflexivity. Qed.
Definition root := Eval vm_compute in match lookup capsule_definitions "kl:buri.eq2-derive" with
 | Some d=>d|None=>Def [] (Lit Nil) end.
Lemma root_binding : lookup capsule_definitions "kl:buri.eq2-derive"=Some root /\ List.length (params root)=1.
Proof. vm_compute;split;reflexivity. Qed.
Theorem sealed_checker_concurrent_sound : forall (D:Type) (constants:nat->D) (application:D->D->D)
 raw p a b wa wb,
 A.admit raw=Some p ->
 NativeRuntime.concurrent_reaches (lookup capsule_definitions)
 ((NativeRuntime.Enter (arguments (params root) [raw]) (body root),[]),wa)
 ((NativeRuntime.Deliver (C.result_value (Some (a,b))),[]),wb) ->
 forall rho,@Equality.denote D constants application rho a=@Equality.denote D constants application rho b.
Proof.
 intros D constants application raw p a b wa wb AD T.
 apply NativeRuntime.erase_rebindings in T;cbn in T.
 destruct (NativeSimulation.trace_execute _ _ _ T) as [steps E].
 assert (NativeRuntime.invoke steps capsule_definitions "kl:buri.eq2-derive" [raw]=Returned (C.result_value (Some (a,b)))) as R.
 { unfold NativeRuntime.invoke;destruct root_binding as [B L];rewrite B,L;exact E. }
 eapply sealed_checker_sound;[exact AD|exact R].
Qed.
Open Scope list_scope.
Definition member name scope := existsb (String.eqb name) scope.
Fixpoint raw_closed fuel scope raw : bool := match fuel with
 | O=>false
 | S n=>match raw with
   | Symbol name=>member name scope
   | Text _ | Integer _ | Boolean _=>true
   | _=>match elements raw with
     | Some [Symbol "quote";_]=>member "quote" scope
     | Some [Symbol "lambda";args;body]=>match elements args with
       | Some xs=>match names xs with Some ns=>member "lambda" scope && raw_closed n (ns++scope) body|_=>false end
       | _=>false end
     | Some [Symbol "let";bindings;body]=>match elements bindings with
       | Some [binding]=>match elements binding with
         | Some [Symbol name;initial]=>member "let" scope && raw_closed n scope initial && raw_closed n (name::scope) body
         | _=>false end
       | _=>false end
     | Some [Symbol "let*";bindings;body]=>match elements bindings with
       | Some bs=>(fix sequence scope bs := match bs with
         | []=>raw_closed n scope body
         | binding::rest=>match elements binding with
           | Some [Symbol name;initial]=>raw_closed n scope initial && sequence (name::scope) rest
           | _=>false end end) scope bs && member "let*" scope
       | _=>false end
     | Some xs=>forallb (raw_closed n scope) xs | _=>false end
   end end.
Definition definition_closed authority raw := match elements raw with
 | Some [Symbol "define";Pair (Symbol _) args;body]=>match elements args with
   | Some xs=>match names xs with
     | Some ns=>raw_closed 100 (ns++map fst C.program++authority) body | _=>false end
   | _=>false end
 | _=>false end.
Theorem raw_identifier_closure : forallb (definition_closed imports) targets=true /\
 raw_closed 100 (map fst C.program++imports) (L [Symbol "lambda";L [Symbol "x";Symbol "y"];
 L [Symbol "equal?";Symbol "x";Symbol "y"]])=true.
Proof. vm_compute;split;reflexivity. Qed.
Theorem missing_cond_is_detected : forallb
 (definition_closed (filter (fun name=>negb (String.eqb name "cond")) imports)) targets=false.
Proof. vm_compute;reflexivity. Qed.
End EqualitySealCorrect.
