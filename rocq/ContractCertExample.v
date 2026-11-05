(* E2E-08: ground derivations of the BURI/KL-CONTRACT-1 checker on the
   certificate of the transported example (ContractTransport, list [1;2;3]),
   and on mutated certificates. Each statement is a single computed run of
   ContractCert.check (vm_compute): ground evidence, not universal. The same
   cases, with the same data and the same fingerprints, are run against the
   Shen checker in tests/contracts.shen (sampled agreement). *)
From Coq Require Import List ZArith NArith String Bool.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLambdaEvaluatorRefinement
 ContractExample ContractTransport ContractCert.
Import ListNotations.
Module ContractCertExample.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics ContractCert.ContractCert.
Module R := KLambdaEvaluatorRefinement.KLambdaEvaluatorRefinement.
Module E := ContractExample.ContractExample.
Module T := ContractTransport.ContractTransport.

Definition example_program (l : list Z) : program :=
 Program [(E.mapn, E.map_params, E.map_body)] (R.tr (T.main_term l)).

Definition sv := SRule RVal [].
Definition prim_call (p : string) (args : list skel) := SRule RCall (SRule AjCtx [SPrim (t p)] :: args).
Definition partial_map := SRule RApp [SRule RCall0 [SRule AjPartial [SSide (t "map-bound")]];
                                      SRule AjPartial [SSide (t "map-bound")]; sv].
Definition body_sk : skel :=
 SRule RIf [prim_call "cons?" [sv];
  SRule RLet [prim_call "hd" [sv];
   SRule RLet [prim_call "tl" [sv];
    SRule RLet [SRule RApp [sv; SRule AjSem [SSide (t "map-fspec")]; sv];
     SRule RLet [SRule RApp [partial_map; SRule AjCtx [SRec E.mapn; SSide (t "map-measure-decreases")]; sv];
      SRule RConseq [prim_call "cons" [sv; sv]]]]]];
  SRule RConseq [sv]].
Fixpoint lit_sk (l : list Z) : skel := match l with [] => sv | _ :: l => prim_call "cons" [sv; lit_sk l] end.
Definition main_sk (l : list Z) : skel :=
 SRule RConseq [SRule RApp [partial_map; SRule AjCtx [SRec E.mapn; SSide (t "dbl-fspec")]; lit_sk l]].

Definition example_cert (l : list Z) (m : cmode) (ms : list (text * text)) (fp : Z) : cert :=
 Cert format_name pinned_theory (t "map-example", fp) pinned_evaluator
   (t "contract_verdict_sound", m) [] ms [(E.mapn, body_sk)] (main_sk l).
Definition l123 := [1; 2; 3]%Z.
Definition good := example_cert l123 CTotal [(E.mapn, t "map_meas")] (fingerprint (example_program l123)).

Theorem example_fingerprint : fingerprint (example_program l123) = 987574484711662929%Z.
Proof. vm_compute. reflexivity. Qed.
Theorem theory_fingerprint : pinned_theory = (t "BURI/KL-CONTRACT-1", 825557597746994086%Z).
Proof. vm_compute. reflexivity. Qed.

Definition prims_of_good := map t ["cons"; "cons"; "cons"; "cons?"; "hd"; "tl"; "cons"]%string.
Definition sides_of_good := map t ["map-bound"; "map-bound"; "dbl-fspec"; "map-fspec"; "map-bound"; "map-bound"; "map-measure-decreases"]%string.

Theorem example_accepted : check (example_program l123) good =
 Accepted (t "contract_verdict_sound", CTotal) [] prims_of_good sides_of_good.
Proof. vm_compute. reflexivity. Qed.
(* A partial-correctness certificate needs no measure (rec_partial). *)
Theorem example_partial_accepted :
 exists ps os, check (example_program l123) (example_cert l123 CPartial [] (fingerprint (example_program l123))) =
   Accepted (t "contract_verdict_sound", CPartial) [] ps os.
Proof. eexists; eexists. vm_compute. reflexivity. Qed.
(* The same skeletons as a total certificate without a measure are refused. *)
Theorem example_missing_measure :
 check (example_program l123) (example_cert l123 CTotal [] (fingerprint (example_program l123))) = Rejected (t "missing-measure").
Proof. vm_compute. reflexivity. Qed.
(* A certificate for [1;2;3] does not cover the program on [1;2;4]. *)
Theorem example_stale_program : check (example_program [1; 2; 4]%Z) good = Rejected (t "stale-program").
Proof. vm_compute. reflexivity. Qed.
Theorem example_stale_theory :
 check (example_program l123) (Cert format_name (t "BURI/KL-CONTRACT-1", 1%Z) (c_program good) pinned_evaluator
   (c_stmt good) [] (c_measures good) (c_bodies good) (c_main good)) = Rejected (t "stale-theory").
Proof. vm_compute. reflexivity. Qed.
Theorem example_stale_evaluator :
 check (example_program l123) (Cert format_name pinned_theory (c_program good) (t "e2e07_klambda", 0%Z)
   (c_stmt good) [] (c_measures good) (c_bodies good) (c_main good)) = Rejected (t "stale-evaluator").
Proof. vm_compute. reflexivity. Qed.
(* A host contract (here a host cons) must be declared; when declared it is
   reported as a premise of the accepted statement, never as discharged. *)
Definition host_main := SRule RConseq [SRule RApp [partial_map; SRule AjCtx [SRec E.mapn; SSide (t "dbl-fspec")];
 SRule RCall [SRule AjCtx [SHyp (t "host:cons")]; sv; lit_sk [2; 3]%Z]]].
Theorem example_undeclared_hyp :
 check (example_program l123) (Cert format_name pinned_theory (c_program good) pinned_evaluator
   (c_stmt good) [] (c_measures good) (c_bodies good) host_main) = Rejected (t "undeclared-hypothesis").
Proof. vm_compute. reflexivity. Qed.
Theorem example_declared_hyp :
 exists ps os, check (example_program l123) (Cert format_name pinned_theory (c_program good) pinned_evaluator
   (c_stmt good) [t "host:cons"] (c_measures good) (c_bodies good) host_main) =
   Accepted (c_stmt good) [t "host:cons"] ps os.
Proof. eexists; eexists. vm_compute. reflexivity. Qed.
Theorem example_unknown_prim :
 check (example_program l123) (Cert format_name pinned_theory (c_program good) pinned_evaluator
   (c_stmt good) [] (c_measures good) (c_bodies good)
   (SRule RConseq [SRule RApp [partial_map; SRule AjCtx [SRec E.mapn]; prim_call "launch" [sv; lit_sk [2; 3]%Z]]])) =
 Rejected (t "unknown-primitive").
Proof. vm_compute. reflexivity. Qed.
(* A rule applied to the wrong syntax: r_if where the body has r_let. *)
Theorem example_body_shape :
 check (example_program l123) (Cert format_name pinned_theory (c_program good) pinned_evaluator
   (c_stmt good) [] (c_measures good)
   [(E.mapn, SRule RIf [prim_call "cons?" [sv]; SRule RIf [sv; sv; sv]; SRule RConseq [sv]])] (c_main good)) =
 Rejected (t "body-shape").
Proof. vm_compute. reflexivity. Qed.
End ContractCertExample.
