(* E2E-05: KLambda values, store and semantic profile. Values are the agreed
   semantic profile, not a Scheme or CL representation; ports must prove a
   representation relation to them (docs/VALUE-MODEL.md, obligation matrix). *)
From Coq Require Import List ZArith NArith String Ascii Bool DecimalString Lia.
From Buri Require Import Observation KLSyntax.
Import ListNotations.
Module KLValue.
Import Observation.Observation KLSyntax.KLSyntax.

(* Exceptions are first-class values (trap-error passes them to handlers).
   Each failure class has its own constructor; messages of system errors are a
   per-port profile slot (sys_message), not part of the agreed semantics. *)
Inductive exn :=
 | XUser (msg : text)              (* simple-error *)
 | XUnboundVar (x : name)          (* ill-scoped resolved syntax *)
 | XUnboundGlobal (x : name)       (* value of an unassigned global *)
 | XUndefinedFun (f : name)        (* call of a name with no function binding *)
 | XNotCallable | XNotBoolean | XArity
 | XPrim (p : prim)                (* primitive applied outside its domain *)
 | XDivZero | XBounds | XCondFail
 | XBadDefinition                  (* defun with repeated parameters *)
 | XIO (e : io_error)
 | XEvalKL.                        (* eval-kl of data that is not KLambda code *)

(* Vectors are heap objects with identity (VVec location). Pairs are immutable
   trees: KLambda has no pair mutation, so pair identity is unobservable.
   Closures capture their lexical environment; VPartial is partial application
   of a named global function and resolves the name when saturated. *)
Inductive value :=
 | VNum (n : num) | VSym (s : name) | VBool (b : bool) | VStr (t : text) | VNil
 | VCons (a d : value)
 | VVec (l : nat)
 | VStream (h : N)
 | VLam (x : name) (body : expr) (env : list (name * value))
 | VFrozen (body : expr) (env : list (name * value))
 | VPartial (f : name) (args : list value)
 | VExn (x : exn).
Definition lenv := list (name * value).

Inductive fundef := FPrim (p : prim) | FUser (params : list name) (body : expr).
Definition fun_arity (d : fundef) : nat := match d with
 | FPrim p => prim_arity p | FUser ps _ => List.length ps end.

(* Store: vector heap, global value namespace (set/value) and global function
   namespace (defun). Namespaces are association lists, newest binding first:
   redefinition is a new head entry, so later lookups see it. *)
Record store := Store {
 heap : list (list value);
 gvals : list (name * value);
 gfuns : list (name * fundef) }.

Fixpoint lookup {A} (x : name) (l : list (name * A)) : option A := match l with
 | [] => None
 | (y, v) :: l => if text_eqb x y then Some v else lookup x l end.

(* The semantic profile. Integer arithmetic, all structural rules and every
   error class are fixed by this file. Inexact (binary64) arithmetic, printing,
   system error messages, uninitialised vector contents, clock conversion and
   resource limits are explicit parameters that a port profile must pin and
   discharge. None of them is an axiom: theorems quantify over every profile. *)
Record profile := Profile {
 inexact_op : prim -> num -> num -> option num;    (* + - * / with an inexact operand *)
 inexact_cmp : prim -> num -> num -> bool;         (* > < >= <= = with an inexact operand *)
 int_div_inexact : Z -> Z -> num;                  (* non-integral exact quotient *)
 float_text : N -> text;                           (* str of an inexact number *)
 str_other : value -> option text;                 (* str of strings, nil, streams, ... *)
 sys_message : exn -> text;                        (* error-to-string of system errors *)
 absvector_fill : value;                           (* initial vector slot contents *)
 time_value : text -> Z -> option num;             (* get-time clock reading conversion *)
 stack_limit : option nat;                         (* program continuation bound *)
 heap_limit : option nat }.                        (* program vector-cell bound *)

(* Numeric operations. *)
Definition int_or (P : profile) (p : prim) (iop : Z -> Z -> Z) (a b : num) : option num :=
 match a, b with NInt x, NInt y => Some (NInt (iop x y)) | _, _ => inexact_op P p a b end.
Definition num_div (P : profile) (a b : num) : option (option num) :=
 (* outer None: division by exact zero; inner None: outside the inexact domain *)
 match a, b with
 | _, NInt 0 => None
 | NInt x, NInt y => Some (Some (if Z.eqb (Z.rem x y) 0 then NInt (Z.quot x y) else int_div_inexact P x y))
 | _, _ => Some (inexact_op P PDiv a b) end.
Definition num_cmp (P : profile) (p : prim) (a b : num) : bool := match a, b with
 | NInt x, NInt y => match p with
   | PGt => Z.gtb x y | PLt => Z.ltb x y | PGe => Z.geb x y | PLe => Z.leb x y
   | _ => Z.eqb x y end
 | _, _ => inexact_cmp P p a b end.

(* Structural equality `=`. Some = defined, None = undefined in the agreed
   profile (closures, exceptions, or vector nesting deeper than the heap,
   which only cyclic structures reach). Vectors at the same location are equal. *)
Fixpoint list_eq (f : value -> value -> option bool) (xs ys : list value) : option bool :=
 match xs, ys with
 | [], [] => Some true
 | x :: xs, y :: ys => match f x y with Some true => list_eq f xs ys | r => r end
 | _, _ => Some false end.

Fixpoint eq_depth (P : profile) (h : list (list value)) (d : nat) {struct d} : value -> value -> option bool :=
 match d with
 | O => fun _ _ => None
 | S d' => fix go (a b : value) {struct a} : option bool :=
   match a, b with
   | VNum x, VNum y => Some (num_cmp P PEqual x y)
   | VSym x, VSym y | VStr x, VStr y => Some (text_eqb x y)
   | VBool x, VBool y => Some (Bool.eqb x y)
   | VNil, VNil => Some true
   | VCons a1 a2, VCons b1 b2 => match go a1 b1 with Some true => go a2 b2 | r => r end
   | VStream x, VStream y => Some (N.eqb x y)
   | VVec l1, VVec l2 => if Nat.eqb l1 l2 then Some true else
       match nth_error h l1, nth_error h l2 with
       | Some xs, Some ys => list_eq (eq_depth P h d') xs ys
       | _, _ => None end
   | (VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _), _ => match b with
       | VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _ => None | _ => Some false end
   | _, (VLam _ _ _ | VFrozen _ _ | VPartial _ _ | VExn _) => Some false
   | _, _ => Some false end end.
Definition kl_eq (P : profile) (h : list (list value)) (a b : value) : option bool :=
 eq_depth P h (S (List.length h)) a b.

(* Printing of exact data. *)
Definition dec_text (z : Z) : text := of_string (NilZero.string_of_int (Z.to_int z)).
Definition bool_text (b : bool) : text := of_string (if b then "true" else "false").

(* Code points: Unicode scalar values. *)
Definition scalar_ok (z : Z) : bool :=
 (Z.leb 0 z && Z.leb z 1114111 && negb (Z.leb 55296 z && Z.leb z 57343))%bool.

(* Heap operations; allocation checks the profile's resource bound. *)
Definition heap_cells (h : list (list value)) : nat := fold_right (fun v n => List.length v + n) 0 h.
Definition alloc_ok (P : profile) (h : list (list value)) (n : nat) : bool :=
 match heap_limit P with None => true | Some m => Nat.leb (heap_cells h + n + 1) m end.
Fixpoint replace_nth {A} (n : nat) (x : A) (l : list A) : list A := match n, l with
 | O, _ :: l => x :: l
 | S n, y :: l => y :: replace_nth n x l
 | _, [] => [] end.
Lemma replace_nth_length : forall A n (x : A) l, List.length (replace_nth n x l) = List.length l.
Proof. induction n; destruct l; cbn; auto. Qed.

(* Well-formed values: every location is allocated in a heap of size n.
   Exceptions and expressions contain no locations. *)
Fixpoint vok (n : nat) (v : value) {struct v} : Prop := match v with
 | VCons a d => vok n a /\ vok n d
 | VVec l => l < n
 | VLam _ _ rho | VFrozen _ rho => fold_right (fun '(_, w) acc => vok n w /\ acc) True rho
 | VPartial _ args => fold_right (fun w acc => vok n w /\ acc) True args
 | _ => True end.
Definition lok n (l : list value) := Forall (vok n) l.
Definition eok n (rho : lenv) := Forall (fun p => vok n (snd p)) rho.

Lemma fold_lok : forall n l, fold_right (fun w acc => vok n w /\ acc) True l <-> lok n l.
Proof.
 induction l as [|a l IH]; cbn; split; intro H.
 - constructor.
 - exact I.
 - destruct H as [A B]; constructor; [exact A|apply IH; exact B].
 - inversion H; subst; split; [assumption|apply IH; assumption].
Qed.
Lemma fold_eok : forall n rho, fold_right (fun '(_, w) acc => vok n w /\ acc) True rho <-> eok n rho.
Proof.
 induction rho as [|[x a] rho IH]; cbn; split; intro H.
 - constructor.
 - exact I.
 - destruct H as [A B]; constructor; [exact A|apply IH; exact B].
 - inversion H; subst; split; [assumption|apply IH; assumption].
Qed.

(* Nested induction principle for values. *)
Section ValueInd.
Variable Pv : value -> Prop.
Hypotheses
 (HNum : forall n, Pv (VNum n)) (HSym : forall s, Pv (VSym s)) (HBool : forall b, Pv (VBool b))
 (HStr : forall t, Pv (VStr t)) (HNil : Pv VNil) (HCons : forall a d, Pv a -> Pv d -> Pv (VCons a d))
 (HVec : forall l, Pv (VVec l)) (HStream : forall h, Pv (VStream h))
 (HLam : forall x b rho, Forall (fun p => Pv (snd p)) rho -> Pv (VLam x b rho))
 (HFrozen : forall b rho, Forall (fun p => Pv (snd p)) rho -> Pv (VFrozen b rho))
 (HPartial : forall f args, Forall Pv args -> Pv (VPartial f args))
 (HExn : forall x, Pv (VExn x)).
Fixpoint value_rect' (v : value) : Pv v :=
 let env_ok := fix go (r : lenv) : Forall (fun p => Pv (snd p)) r := match r with
   | [] => Forall_nil _
   | p :: r => Forall_cons p (match p as p0 return Pv (snd p0) with (_, w) => value_rect' w end) (go r) end in
 match v with
 | VNum n => HNum n | VSym s => HSym s | VBool b => HBool b | VStr t => HStr t | VNil => HNil
 | VCons a d => HCons a d (value_rect' a) (value_rect' d)
 | VVec l => HVec l | VStream h => HStream h
 | VLam x b rho => HLam x b rho (env_ok rho)
 | VFrozen b rho => HFrozen b rho (env_ok rho)
 | VPartial f args => HPartial f args ((fix go (l : list value) : Forall Pv l := match l with
     | [] => Forall_nil _ | w :: l => Forall_cons w (value_rect' w) (go l) end) args)
 | VExn x => HExn x end.
End ValueInd.

Lemma vok_mono : forall v n m, n <= m -> vok n v -> vok m v.
Proof.
 intro v; induction v using value_rect'; intros n0 m L K; cbn in *; auto; try lia.
 - destruct K; split; eauto.
 - apply fold_eok in K; apply fold_eok. revert K; induction H; intro K; inversion K; subst; constructor; (eapply H; eassumption) || (apply IHForall; assumption).
 - apply fold_eok in K; apply fold_eok. revert K; induction H; intro K; inversion K; subst; constructor; (eapply H; eassumption) || (apply IHForall; assumption).
 - apply fold_lok in K; apply fold_lok. revert K; induction H; intro K; inversion K; subst; constructor; (eapply H; eassumption) || (apply IHForall; assumption).
Qed.
Lemma lok_mono : forall n m l, n <= m -> lok n l -> lok m l.
Proof. intros; eapply Forall_impl; [|eassumption]; intros; eapply vok_mono; eauto. Qed.
Lemma eok_mono : forall n m l, n <= m -> eok n l -> eok m l.
Proof. intros; eapply Forall_impl; [|eassumption]; intros; eapply vok_mono; eauto. Qed.

Lemma lookup_ok : forall n x rho v, eok n rho -> lookup x rho = Some v -> vok n v.
Proof.
 induction rho as [|[y w] rho IH]; cbn; intros v H E; [discriminate|].
 inversion H; subst. destruct (text_eqb x y); [inversion E; subst; assumption|eauto].
Qed.

(* A store is well formed when every stored value points into its heap. *)
Definition store_ok (s : store) :=
 Forall (lok (List.length (heap s))) (heap s) /\ eok (List.length (heap s)) (gvals s).
End KLValue.
