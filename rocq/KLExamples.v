(* Ground derivations of the KLambda semantics under one concrete profile and
   concrete environments. These are executions of the Rocq rule table, not
   universal theorems and not evidence about any port. *)
From Coq Require Import List ZArith NArith String Bool.
From Buri Require Import Observation KLSyntax KLValue KLSemantics KLMetatheory.
Import ListNotations.
Module KLExamples.
Import Observation.Observation KLSyntax.KLSyntax KLValue.KLValue KLSemantics.KLSemantics KLMetatheory.KLMetatheory.
Open Scope string_scope.

Definition t := of_string.
(* An exact-only profile: every inexact operation is outside its domain. *)
Definition P0 : profile := Profile (fun _ _ _ => None) (fun _ _ _ => false)
 (fun _ _ => NInt 0) (fun _ => t "<float>") (fun _ => None) (fun _ => t "system-error")
 (VSym (t "shen.fail!")) (fun _ z => Some (NInt z)) None None.

Definition prim_table : list (name * fundef) := map (fun p => (t (prim_name p), FPrim p)) all_prims.
Definition s0 : store := Store [] [(t "*stoutput*", VStream 1)] prim_table.

(* Environments: one that answers every write with the given response and
   every read from a byte list. *)
Definition env := (list N * response)%type.
Definition respond (w : env) (q : request) : response * env := match q with
 | QWrite _ _ => (snd w, w)
 | QRead _ _ => match fst w with [] => (REof, w) | b :: bs => (RRead [b], (bs, snd w)) end
 | QOpen _ _ => (ROpened 7, w)
 | QClose _ => (RClosed, w)
 | QTime _ => (RTime 42, w)
 | QRandom _ => (RRandom 4, w) end.
Definition quiet (_ : env) : option env_event := None.
Definition go (fuel : nat) (e : expr) (w : env) :=
 run env respond quiet (fun w => w) P0 fuel (Cfg (Eval [] e) [] s0) w.
Definition w0 : env := ([], RWrote 1).

Definition call (f : string) (args : list expr) := ECall (t f) args.
Definition var (x : string) := EVar (t x).
Definition int (z : Z) := ENum (NInt z).

Definition fact_def := EDefun (t "fact") [t "n"]
 (EIf (call "=" [var "n"; int 0]) (int 1)
   (call "*" [var "n"; call "fact" [call "-" [var "n"; int 1]]])).

Example factorial : go 400 (ELet (t "d") fact_def (call "fact" [int 5])) w0 = VDone [] (Normal (VNum (NInt 120))).
Proof. vm_compute; reflexivity. Qed.

Example currying : go 50 (EApp (call "+" [int 1]) [int 2]) w0 = VDone [] (Normal (VNum (NInt 3))).
Proof. vm_compute; reflexivity. Qed.

Example over_application :
 go 50 (EApp (ELam (t "x") (ELam (t "y") (var "y"))) [int 1; int 2]) w0 = VDone [] (Normal (VNum (NInt 2))).
Proof. vm_compute; reflexivity. Qed.

Example trap_and_message :
 go 50 (ETrap (call "simple-error" [EStr (t "boom")]) (ELam (t "e") (call "error-to-string" [var "e"]))) w0
 = VDone [] (Normal (VStr (t "boom"))).
Proof. vm_compute; reflexivity. Qed.

Example left_to_right :
 go 50 (call "cons" [call "simple-error" [EStr (t "left")]; call "simple-error" [EStr (t "right")]]) w0
 = VDone [] (Error (XUser (t "left"))).
Proof. vm_compute; reflexivity. Qed.

Example redefinition :
 go 80 (ELet (t "a") (EDefun (t "f") [t "x"] (int 1))
        (ELet (t "b") (EDefun (t "f") [t "x"] (int 2)) (call "f" [int 0]))) w0
 = VDone [] (Normal (VNum (NInt 2))).
Proof. vm_compute; reflexivity. Qed.

Example vector_aliasing :
 go 80 (ELet (t "v") (call "absvector" [int 1]) (ELet (t "w") (var "v")
   (ELet (t "u") (call "address->" [var "w"; int 0; int 7]) (call "<-address" [var "v"; int 0])))) w0
 = VDone [] (Normal (VNum (NInt 7))).
Proof. vm_compute; reflexivity. Qed.

Example vector_bounds :
 go 50 (call "<-address" [call "absvector" [int 1]; int 3]) w0 = VDone [] (Error XBounds).
Proof. vm_compute; reflexivity. Qed.

Example cond_fallthrough : go 20 (ECond [(EBool false, int 1)]) w0 = VDone [] (Error XCondFail).
Proof. vm_compute; reflexivity. Qed.

Example nonboolean_if : go 20 (EIf (int 0) (int 1) (int 2)) w0 = VDone [] (Error XNotBoolean).
Proof. vm_compute; reflexivity. Qed.

Example closure_equality_undefined :
 go 30 (call "=" [ELam (t "x") (var "x"); ELam (t "x") (var "x")]) w0 = VWrong [].
Proof. vm_compute; reflexivity. Qed.

Example eval_kl_data :
 go 50 (call "eval-kl" [call "cons" [ESym (t "+"); call "cons" [int 1; call "cons" [int 2; ENil]]]]) w0
 = VDone [] (Normal (VNum (NInt 3))).
Proof. vm_compute; reflexivity. Qed.

Example write_success :
 go 30 (call "write-byte" [int 65; call "value" [ESym (t "*stoutput*")]]) w0
 = VDone [EvIO (QWrite 1 [65%N]) (RWrote 1)] (Normal (VNum (NInt 65))).
Proof. vm_compute; reflexivity. Qed.

(* A failed write is observed in the trace and raised as a structured error. *)
Example write_failure :
 go 30 (call "write-byte" [int 65; call "value" [ESym (t "*stoutput*")]]) ([], RFailed ENoSpace)
 = VDone [EvIO (QWrite 1 [65%N]) (RFailed ENoSpace)] (Error (XIO ENoSpace)).
Proof. vm_compute; reflexivity. Qed.

Example partial_write :
 go 30 (call "write-byte" [int 65; call "value" [ESym (t "*stoutput*")]]) ([], RWrote 0)
 = VDone [EvIO (QWrite 1 [65%N]) (RWrote 0)] (Error (XIO EShortWrite)).
Proof. vm_compute; reflexivity. Qed.

Example read_then_eof :
 go 40 (call "cons" [call "read-byte" [EVar (t "s")]; int 0]) w0 = VDone [] (Error (XUnboundVar (t "s"))).
Proof. vm_compute; reflexivity. Qed.

Example open_and_read :
 go 40 (call "read-byte" [call "open" [EStr (t "f"); ESym (t "in")]]) ([9%N], RWrote 1)
 = VDone [EvIO (QOpen (t "f") DIn) (ROpened 7); EvIO (QRead 7 1) (RRead [9%N])] (Normal (VNum (NInt 9))).
Proof. vm_compute; reflexivity. Qed.

Example small_fuel_exhausts : go 0 (EIf (EBool true) (int 1) (int 2)) w0 = VExhausted [].
Proof. vm_compute; reflexivity. Qed.
Example enough_fuel_decides : go 5 (EIf (EBool true) (int 1) (int 2)) w0 = VDone [] (Normal (VNum (NInt 1))).
Proof. vm_compute; reflexivity. Qed.

(* Universal consequence of the ground facts above: an exhausted run is not
   evidence of divergence. *)
Theorem exhaustion_does_not_imply_divergence :
 exists c w, run env respond quiet (fun w => w) P0 0 c w = VExhausted [] /\
  ~ behaves (rstep env respond quiet (fun w => w) P0) (cfinal env P0) (c, w) (Diverges []).
Proof.
 exists (Cfg (Eval [] (EIf (EBool true) (int 1) (int 2))) [] s0), w0; split; [exact small_fuel_exhausts|].
 intro D. destruct (divergence_exhausts_every_fuel env respond quiet (fun w => w) P0 _ _ _ D 5) as [u R].
 change (go 5 (EIf (EBool true) (int 1) (int 2)) w0 = VExhausted u) in R.
 rewrite enough_fuel_decides in R; discriminate.
Qed.
End KLExamples.
